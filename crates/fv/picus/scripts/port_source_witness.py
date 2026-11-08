#!/usr/bin/env python3
"""Bounded, fail-closed source-equality audit of authentic generated Ziren Lean.

This is a research diagnostic, not a Lean proof or a production pinning guard.
It relies on the current emitted equality shape and on the generator's witness
field annotations as temporary source-name proxies. Column-insertion stability
is NOT established by this experiment.
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


def module_body(source: str, module: str) -> str:
    start = f"\nnamespace {module}\n"
    end = f"\nend {module}"
    if source.count(start) != 1:
        raise Unwitnessed(f"module {module!r} is not unique")
    body = source.split(start, 1)[1]
    if body.count(end) != 1:
        raise Unwitnessed(f"end marker of {module!r} is not unique")
    return body.split(end, 1)[0]


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

    # A temporary naming proxy from the exact generator's W declarations.
    # It is not yet the source-qualified name_to_colrange mapping.
    names = re.findall(r'/-- `([^`]+)` -/\s*\n\s*v(\d+) : F', body)
    if (len({name for name, _ in names}) != len(names)
            or len({var_id for _, var_id in names}) != len(names)):
        raise Unwitnessed("duplicate source field name or variable annotation")
    names_by_id = {var_id: name for name, var_id in names}

    # Parse only direct equality binders emitted in the current Lean format:
    #   (w.v306 - <rhs>) = 0
    # A missing or repeated binder is UNKNOWN, never silently accepted.
    matches = re.findall(r'^\s*\(w\.v(\d+) - (.+)\) = 0(?: ∧)?$', body, re.M)
    rhs_by_id: dict[str, list[str]] = {}
    for var_id, rhs in matches:
        rhs_by_id.setdefault(var_id, []).append(rhs)

    def canonical(rhs: str) -> str:
        def replace_var(match: re.Match[str]) -> str:
            var_id = match.group(1)
            if var_id not in names_by_id:
                raise Unwitnessed(f"unmapped variable in binding expression: v{var_id}")
            return f"@{names_by_id[var_id]}"

        normalized = re.sub(r'w\.v(\d+)', replace_var, rhs)
        return re.sub(r'\s+', '', normalized)

    result = {}
    for label, port in zip(labels, ports):
        var_id = port.removeprefix("w.v")
        matches_for_port = rhs_by_id.get(var_id, [])
        if len(matches_for_port) == 1:
            result[label] = Witness(label, canonical(matches_for_port[0]))
        elif len(matches_for_port) > 1:
            raise Unwitnessed(f"multiple candidate equalities for {label}")
    return result


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
