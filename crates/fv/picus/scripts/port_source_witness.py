#!/usr/bin/env python3
"""Bounded, fail-closed source-equality audit of authentic generated Ziren Lean.

This is a research diagnostic, not a Lean proof or a production pinning guard.
It relies on the current emitted equality shape and the generator's field-relative
witness annotations. Source insertion invariance is established only for the
bounded AddSub experiment, not for arbitrary chips or expression trees.
"""

import argparse
import re
import sys
from dataclasses import dataclass


class Unwitnessed(ValueError):
    """A claimed source binding cannot be recovered unambiguously."""


@dataclass(frozen=True)
class Witness:
    origin: str
    expression: str


def enclosing_parens(expression: str) -> bool:
    """Require a single balanced outer pair; a prefix/suffix check is unsafe."""
    if not expression.startswith("(") or not expression.endswith(")"):
        return False
    depth = 0
    for i, char in enumerate(expression):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0 or depth == 0 and i != len(expression) - 1:
                return False
    return depth == 0


def discard_proven_multiplicative_one(expression: str) -> str:
    """Normalize only a *top-level* multiplication by the field's literal one."""
    while enclosing_parens(expression):
        interior = expression[1:-1]
        depth = 0
        split = None
        for i, char in enumerate(interior):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth < 0:
                    return expression
            elif char == "*" and depth == 0:
                if split is not None:
                    return expression
                split = i
        if depth != 0 or split is None or interior[split + 1:] != "(1:F)":
            return expression
        expression = interior[:split]
    return expression


def module_body(source: str, module: str) -> str:
    start = f"\nnamespace {module}\n"
    end = f"\nend {module}"
    if source.count(start) != 1:
        raise Unwitnessed(f"module {module!r} is not unique")
    body = source.split(start, 1)[1]
    if body.count(end) != 1:
        raise Unwitnessed(f"end marker of {module!r} is not unique")
    return body.split(end, 1)[0]


def active_constraint_text(body: str) -> str:
    """Read equalities only from the emitted active constraints definition(s)."""
    blocks: dict[str, str] = {}
    pattern = r'(?m)^def (constraints(?:_\d+)?) \(w : W\) : Prop :=\n((?:[ \t]+[^\n]*(?:\n|$))+)'
    for match in re.finditer(pattern, body):
        key, value = match.groups()
        if key in blocks:
            raise Unwitnessed(f"duplicate constraint definition: {key}")
        if '/-' in value or '--' in value:
            raise Unwitnessed("comments inside constraint definitions are not qualified")
        blocks[key] = value
    if "constraints" not in blocks:
        raise Unwitnessed("missing active constraints definition")

    master = blocks["constraints"].strip()
    if re.search(r'\bconstraints_\d+\b', master):
        used = [x.strip() for x in master.split('∧')]
        if (len(used) != len(set(used)) or
                any(not re.fullmatch(r'constraints_\d+ w', x) for x in used)):
            raise Unwitnessed("ambiguous active constraints fan-in")
        names = [x.removesuffix(' w') for x in used]
        if any(name not in blocks for name in names):
            raise Unwitnessed("referenced constraints block missing")
        return '\n'.join(blocks[name] for name in names)
    # The small synthetic controls use a direct conjunction. The authentic
    # AddSub generator uses numbered blocks joined by the master definition.
    return master


def source_witnesses(source: str, module: str = "AddSub_is_add") -> dict[str, Witness]:
    body = module_body(source, module)
    origin_match = re.search(r'^def output_origins : List String := \[(.*)\]$', body, re.M)
    output_match = re.search(r'^def outputs \(w : W\) : List F :=\s*\n\s*\[([^\]]+)\]', body, re.M)
    if not origin_match or not output_match:
        raise Unwitnessed("missing emitted output labels or values")
    labels = re.findall(r'"([^"\n]+)"', origin_match.group(1))
    ports = [p.strip() for p in output_match.group(1).split(",")]
    if len(labels) != len(ports) or len(labels) != len(set(labels)):
        raise Unwitnessed("output origin/value count mismatch or duplicated label")
    if any(not re.fullmatch(r'w\.v\d+', p) for p in ports):
        raise Unwitnessed("non-variable output expression")

    # Field-relative annotations emitted by the exact generator from
    # PicusInfo.name_to_colrange. Treat ambiguous annotations as UNKNOWN.
    names = re.findall(r'/-- `([^`]+)` -/\s*\n\s*v(\d+) : F', body)
    if (len({name for name, _ in names}) != len(names)
            or len({var_id for _, var_id in names}) != len(names)):
        raise Unwitnessed("duplicate source field name or variable annotation")
    names_by_id = {var_id: name for name, var_id in names}

    # Parse only direct equality binders emitted in the current Lean format:
    #   (w.v306 - <rhs>) = 0
    # A missing or repeated binder is UNKNOWN, never silently accepted.
    matches = re.findall(r'^\s*\(w\.v(\d+) - (.+)\) = 0(?: ∧)?$',
                         active_constraint_text(body), re.M)
    rhs_by_id: dict[str, list[str]] = {}
    for var_id, rhs in matches:
        rhs_by_id.setdefault(var_id, []).append(rhs)

    expansions = [0]

    def canonical(rhs: str, stack: frozenset[str] = frozenset()) -> str:
        def replace_var(match: re.Match[str]) -> str:
            var_id = match.group(1)
            if var_id in names_by_id:
                return f"@{names_by_id[var_id]}"
            candidates = rhs_by_id.get(var_id, [])
            if len(candidates) != 1 or var_id in stack:
                raise Unwitnessed(f"missing, ambiguous or cyclic intermediate equality: v{var_id}")
            expansions[0] += 1
            if expansions[0] > 4096:
                raise Unwitnessed("intermediate equality expansion budget exceeded")
            candidate = candidates[0].strip()
            # Lean's emitted arithmetic expressions are parenthesized. Refuse
            # an unbracketed composite, whose textual substitution could
            # silently change operator precedence.
            if not (enclosing_parens(candidate)
                    or re.fullmatch(r'w\.v\d+', candidate)):
                raise Unwitnessed(f"unparenthesized intermediate: v{var_id}")
            return canonical(candidate, stack | {var_id})

        normalized = re.sub(r'w\.v(\d+)', replace_var, rhs)
        return discard_proven_multiplicative_one(re.sub(r'\s+', '', normalized))

    result = {}
    for label, port in zip(labels, ports):
        var_id = port.removeprefix("w.v")
        matches_for_port = rhs_by_id.get(var_id, [])
        if len(matches_for_port) == 1:
            result[label] = Witness(label, canonical(matches_for_port[0]))
        elif len(matches_for_port) > 1:
            raise Unwitnessed(f"multiple candidate equalities for {label}")
        elif var_id in names_by_id:
            # A port that directly exports an original AIR column needs no
            # introduced equality. Its stable field-relative name is the
            # source identity; a derived unannotated free variable is UNKNOWN.
            result[label] = Witness(label, f"@{names_by_id[var_id]}")
    return result


def compare_sources(old_source: str, new_source: str,
                    module: str = "AddSub_is_add") -> tuple[str, list[str]]:
    """Classify two generated source interfaces; missing binding evidence is UNKNOWN.

    This is deliberately a bounded source-equality comparator, not a proof
    checker and not an automatic replacement for the v1 manifest guard.
    """
    def qualified(source: str) -> tuple[list[str], dict[str, Witness]]:
        body = module_body(source, module)
        declaration = re.search(r'^def output_origins : List String := \[(.*)\]$',
                                body, re.M)
        if declaration is None:
            raise Unwitnessed("missing output provenance")
        labels = re.findall(r'"([^"\n]+)"', declaration.group(1))
        bindings = source_witnesses(source, module)
        if len(set(labels)) != len(labels):
            raise Unwitnessed("duplicate port provenance")
        return labels, bindings

    try:
        old_labels, old = qualified(old_source)
        new_labels, new = qualified(new_source)
    except Unwitnessed:
        return "UNKNOWN", ["<unqualified interface>"]

    lost_or_gained = set(old_labels) ^ set(new_labels)
    if lost_or_gained:
        return "REVIEW_REQUIRED", sorted(lost_or_gained)
    unresolved = {label for label in old_labels if label not in old or label not in new}
    changed = {label for label in old_labels if label in old and label in new
               and old[label].expression != new[label].expression}
    if changed:
        return "REVIEW_REQUIRED", sorted(changed | unresolved)
    if unresolved:
        return "UNKNOWN", sorted(unresolved)
    return "UNCHANGED", []


def _replace_rhs(source: str, port_id: str, replacement: str) -> str:
    pattern = rf'(?m)^(\s*\(w\.v{port_id} - )(.+)(\) = 0(?: ∧)?)$'
    out, count = re.subn(pattern, lambda m: m.group(1) + replacement + m.group(3), source)
    if count != 1:
        raise AssertionError(f"cannot rewrite port v{port_id}: found {count} equalities")
    return out


def selftest(source: str) -> dict[str, str]:
    baseline = source_witnesses(source)
    a, b = "state_send[1]", "state_send[3]"
    if a not in baseline or b not in baseline or baseline[a] == baseline[b]:
        raise AssertionError("authentic derived ports are not independently witnessed")
    if "@frame[" not in baseline[a].expression or "@next_pc[" not in baseline[b].expression:
        raise AssertionError("source names are not field-relative: v2 baseline unqualified")

    # Consequential rebind: same emitted port labels and values, swapped right-hand sides.
    body = module_body(source, "AddSub_is_add")
    eqs = dict(re.findall(r'^\s*\(w\.v(\d+) - (.+)\) = 0(?: ∧)?$', body, re.M))
    if "306" not in eqs or "307" not in eqs:
        raise AssertionError("authentic AddSub binders changed: requalify experiment")
    changed = _replace_rhs(_replace_rhs(source, "306", eqs["307"]), "307", eqs["306"])
    altered = source_witnesses(changed)
    if altered[a] == baseline[a] or altered[b] == baseline[b]:
        raise AssertionError("derived-port rebind escaped witness comparison")

    # Benign fresh-variable alpha renaming: change the bound variable everywhere,
    # leaving its source expression and origin invariant.
    renumbered = re.sub(r'\bv(306|307|308)\b',
                        lambda m: "v" + str(int(m.group(1)) + 100), source)
    if source_witnesses(renumbered) != baseline:
        raise AssertionError("fresh-variable alpha renumbering caused a false positive")

    # Simulated insertion shifts all witness variable IDs; the source field-relative
    # identifiers remain unchanged. This is not an actual Rust AIR source edit.
    shifted = re.sub(r'\bv(\d+)\b',
                     lambda m: "v" + str(int(m.group(1)) + 1000), source)
    if source_witnesses(shifted) != baseline:
        raise AssertionError("synthetic column-index shift caused a false positive")

    # Fail closed when the emitted equation is gone: no equality witness for a.
    missing = re.sub(r'(?m)^\s*\(w\.v306 - .+\) = 0 ∧\n', "", source)
    if missing == source or a in source_witnesses(missing):
        raise AssertionError("missing equality was silently accepted")

    # Source-name collisions are not a license to equate distinct variables.
    field_tags = re.findall(r'/-- `([^`]+)` -/\s*\n\s*v\d+ : F',
                            module_body(source, "AddSub_is_add"))
    if len(field_tags) < 2:
        raise AssertionError("authentic field annotation set changed")
    duplicated_name = source.replace(f"/-- `{field_tags[0]}` -/",
                                     f"/-- `{field_tags[1]}` -/", 1)
    try:
        source_witnesses(duplicated_name)
    except Unwitnessed:
        pass
    else:
        raise AssertionError("duplicate source annotation was silently accepted")

    return {a: baseline[a].expression, b: baseline[b].expression}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", default="AddSub_is_add")
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    source = sys.stdin.read()
    try:
        witnesses = selftest(source) if args.selftest else {
            origin: v.expression for origin, v in source_witnesses(source, args.module).items()
        }
    except (Unwitnessed, AssertionError) as e:
        print(f"SOURCE_WITNESS_UNKNOWN: {e}", file=sys.stderr)
        return 1
    for origin, expression in sorted(witnesses.items()):
        print(f"SOURCE_EQ_WITNESSED: {origin} <- {expression}")
    if args.selftest:
        print("SOURCE_EQ_CONTROLS_OK: rebind detected; fresh and synthetic full-index renumbering retained; missing equality and duplicate names UNKNOWN")
        print("BOUNDARY: authentic Lean output + synthetic mutations; real AIR field insertion and semantics not proven")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
