"""Fail-closed bounded arithmetic replay of authentic generated AddSub Lean.

Not a Lean kernel proof. Qualifies only equality/conjunction/range expressions
found in the pinned AddSub_is_add emitter and ZMod 2130706433 field semantics.
"""

import argparse
import ast
import hashlib
import json
import operator
import re
from pathlib import Path

import port_source_witness as source_reader

FIELD_MODULUS = 2130706433
MODULE = "AddSub_is_add"
FIELD = re.compile(r"^  v(\d+) : F$", re.M)
EQUATION = re.compile(r"^\(w\.v(\d+) - (.+)\) = 0$")
ZERO = re.compile(r"^w\.v(\d+) = 0$")
RANGE = re.compile(r"^(.+)\.val ≤ (\d+)$")
INV_CAST = re.compile(r"\(\((\d+) : F\)⁻¹\)")
CAST = re.compile(r"\((-?\d+) : F\)")
VAR = re.compile(r"w\.v(\d+)")
BINOPS = {ast.Add: operator.add, ast.Sub: operator.sub, ast.Mult: operator.mul}


class Unqualified(ValueError):
    """Unsupported generated expression or ambiguous source structure."""


def _arithmetic(expression: str, values: dict[int, int]) -> int:
    """Evaluate a whitelist of integer syntax in the declared finite field."""
    normalized = INV_CAST.sub(lambda m: f"inv({m.group(1)})", expression)
    normalized = CAST.sub(lambda m: m.group(1), normalized)
    normalized = VAR.sub(lambda m: f"v[{m.group(1)}]", normalized)
    if ": F" in normalized or "w." in normalized or "⁻¹" in normalized:
        raise Unqualified(f"unsupported field expression {expression!r}")
    try:
        tree = ast.parse(normalized, mode="eval")
    except SyntaxError as err:
        raise Unqualified(f"invalid field expression {expression!r}") from err

    def walk(node: ast.AST) -> int:
        if isinstance(node, ast.Expression):
            return walk(node.body)
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return node.value
        if isinstance(node, ast.BinOp) and type(node.op) in BINOPS:
            return BINOPS[type(node.op)](walk(node.left), walk(node.right)) % FIELD_MODULUS
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -walk(node.operand) % FIELD_MODULUS
        if (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name)
                and node.value.id == "v" and isinstance(node.slice, ast.Constant)
                and type(node.slice.value) is int):
            try:
                return values[node.slice.value]
            except KeyError as err:
                raise Unqualified(f"unsolved or undeclared witness v{node.slice.value}") from err
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == "inv" and len(node.args) == 1
                and not node.keywords):
            denominator = walk(node.args[0]) % FIELD_MODULUS
            if denominator == 0:
                raise Unqualified("division by zero in field emitter")
            return pow(denominator, -1, FIELD_MODULUS)
        raise Unqualified(f"unqualified arithmetic AST {ast.dump(node)}")

    return walk(tree) % FIELD_MODULUS


def _ports(body: str, port_name: str, values: dict[int, int]) -> list[int]:
    pattern = rf"^def {port_name} \(w : W\) : List F :=\s*\n\s*\[([^\]\n]+)\]$"
    matches = re.findall(pattern, body, re.M)
    if len(matches) != 1:
        raise Unqualified(f"ambiguous {port_name} declaration")
    expressions = [x.strip() for x in matches[0].split(",")]
    if not expressions or any(not re.fullmatch(r"w\.v\d+", x) for x in expressions):
        raise Unqualified(f"unsupported {port_name} port expression")
    origins_name = "input_origins" if port_name == "inputs" else "output_origins"
    origin_lines = re.findall(rf'^def {origins_name} : List String := \[([^\n]+)\]$', body, re.M)
    if len(origin_lines) != 1:
        raise Unqualified(f"missing or duplicated {origins_name}")
    origins = re.findall(r'"([^"\n]+)"', origin_lines[0])
    if len(origins) != len(expressions) or len(origins) != len(set(origins)):
        raise Unqualified(f"ambiguous {origins_name} / port mapping")
    expected = (21, "state_recv[0]", "w.v493") if port_name == "inputs" else (
        0, "state_send[0]", "w.v474")
    idx, origin, variable = expected
    if len(origins) <= idx or (origins[idx], expressions[idx]) != (origin, variable):
        raise Unqualified(f"expected external {origin} is not bound to {variable}")
    return [values[int(x[3:])] for x in expressions]


def evaluate(source: str, frame0: int) -> dict:
    if not 0 <= frame0 < FIELD_MODULUS:
        raise Unqualified("frame0 must be a canonical field representative")
    try:
        body = source_reader.module_body(source, MODULE)
        active = source_reader.active_constraint_text(body)
    except source_reader.Unwitnessed as err:
        raise Unqualified(str(err)) from err
    declared = list(map(int, FIELD.findall(body)))
    if not declared or len(declared) != len(set(declared)):
        raise Unqualified("empty or duplicated witness fields")
    terms = [line.strip().removesuffix(" ∧").strip()
             for line in active.splitlines() if line.strip()]
    if not terms:
        raise Unqualified("empty active conjunct")

    # Parse and qualify every active conjunct before determining any model.
    equations: dict[int, str] = {}
    zeros: set[int] = set()
    checked = []
    for term in terms:
        if term == "False":
            checked.append(("false", term, None))
        elif match := EQUATION.fullmatch(term):
            idx, rhs = int(match.group(1)), match.group(2)
            if idx in equations or idx not in declared:
                raise Unqualified(f"ambiguous or undeclared assigned v{idx}")
            equations[idx] = rhs
            checked.append(("equation", term, (idx, rhs)))
        elif match := ZERO.fullmatch(term):
            idx = int(match.group(1))
            if idx not in declared:
                raise Unqualified(f"undeclared zero v{idx}")
            zeros.add(idx)
            checked.append(("zero", term, idx))
        elif match := RANGE.fullmatch(term):
            checked.append(("range", term, (match.group(1), int(match.group(2)))))
        else:
            raise Unqualified(f"unsupported active conjunct: {term!r}")

    # The current authentic emitter exposes original frame/selector columns
    # in 0..35; all higher columns must be uniquely solved, or explicitly 0.
    values = {idx: 0 for idx in declared if idx <= 35}
    if 2 not in values or 6 not in values or 22 not in values or 28 not in values:
        raise Unqualified("pinned source field identity changed")
    values.update({2: 1, 6: frame0, 22: 2, 28: 1})
    values.update({idx: 0 for idx in zeros if idx not in equations})
    pending = dict(equations)
    while pending:
        progressed = False
        for idx, rhs in list(pending.items()):
            try:
                values[idx] = _arithmetic(rhs, values)
            except Unqualified as err:
                if "unsolved or undeclared witness" in str(err):
                    continue
                raise
            del pending[idx]
            progressed = True
        if not progressed:
            raise Unqualified(f"cyclic or unresolved generated fields {list(pending)}")
    if set(declared) != set(values):
        raise Unqualified(f"unconstrained generated fields {sorted(set(declared) - set(values))}")

    failures: list[str] = []
    for kind, term, payload in checked:
        if kind == "false":
            failures.append(term)
        elif kind == "equation":
            idx, rhs = payload
            if (values[idx] - _arithmetic(rhs, values)) % FIELD_MODULUS != 0:
                failures.append(term)
        elif kind == "zero":
            if values[payload] != 0:
                failures.append(term)
        elif kind == "range":
            expression, limit = payload
            if _arithmetic(expression, values) > limit:
                failures.append(term)
    return {
        "field_modulus": FIELD_MODULUS,
        "module": MODULE,
        "source_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
        "frame0": frame0,
        "constraint_count": len(checked),
        "failed": failures,
        "inputs": _ports(body, "inputs", values),
        "outputs": _ports(body, "outputs", values),
        "assignments": {f"v{idx}": values[idx] for idx in sorted(values)},
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("generated_addsub_lean", type=Path)
    args = ap.parse_args()
    source = args.generated_addsub_lean.read_text(encoding="utf-8")
    range_fact = "  ((w.v6 * w.v408)).val ≤ 65535 ∧\n"
    false_head = "def constraints_0 (w : W) : Prop :=\n"
    if source.count(range_fact) != 1 or source.count(false_head) < 1:
        raise Unqualified("target mutations do not have qualified source anchors")
    cases = {
        "baseline_zero": evaluate(source, 0),
        "baseline_overflow": evaluate(source, 65536),
        "range_removed_overflow": evaluate(source.replace(range_fact, "", 1), 65536),
        "active_false_zero": evaluate(source.replace(false_head, false_head + "  False ∧\n", 1), 0),
    }
    exclusion_anchors = (
        "  (w.v408 - (1 : F)) = 0 ∧\n",
        "  (w.v452 - (1 : F)) = 0 ∧\n",
        "  (w.v493 - (w.v6 * w.v452)) = 0 ∧\n",
    )
    if any(anchor not in source for anchor in exclusion_anchors):
        raise Unqualified("source no longer entails state_recv[0] = frame0")
    if (cases["baseline_zero"]["failed"] or
            cases["baseline_overflow"]["failed"] != [range_fact.strip().removesuffix(" ∧")] or
            cases["range_removed_overflow"]["failed"] or
            cases["active_false_zero"]["failed"] != ["False"] or
            cases["range_removed_overflow"]["inputs"][21] != 65536):
        raise AssertionError("expected bounded separation certificate did not hold")
    print(json.dumps({
        "certificate": "BOUNDED_SOURCE_FIELD_SEPARATION",
        "qualification": "Arithmetic evaluation of every emitted AddSub_is_add conjunct; not Lean kernel check",
        "exclusion": "Original v408=1, v452=1, v493=v6 and v6.val<=65535 exclude any input state_recv[0]=65536",
        "cases": cases,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
