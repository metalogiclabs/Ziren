"""Executable v2 port-identity design spike; not wired into Ziren's checker.

The caller MUST supply source expressions and original-field names from the
generator, not infer them from v1's `derived` names.  Temporary reification
variables must be expanded through the generator's recorded bindings.  Missing
or ambiguous evidence is UNKNOWN, never an unchanged-source certificate.

This only compares syntactic source expressions.  It cannot establish the
functional semantics of the chip constraints or a Lean proof's claim fidelity.
"""

import json


def stable_names_from_ranges(ranges):
    """Represent PicusInfo.name_to_colrange by field-relative source paths.

    Unlike col_to_name's absolute numeric suffix, `field[offset]` survives
    insertion of another field earlier in the AIR layout.  Overlap, invalid
    ranges or ambiguous field identities cannot qualify a source map.
    """
    if not isinstance(ranges, dict):
        return None
    names = {}
    for field, bounds in ranges.items():
        if (not isinstance(field, str) or not field
                or not isinstance(bounds, (tuple, list)) or len(bounds) != 2):
            return None
        start, end = bounds
        if (type(start) is not int or type(end) is not int
                or start < 0 or end <= start or end - start > 1_000_000):
            return None
        for offset, col in enumerate(range(start, end)):
            if col in names:
                return None
            names[col] = f"{field}[{offset}]"
    return names


def signature(expr, names, bindings):
    """Canonical source expression or None if its identity is not qualified.

    Term form mirrors PicusExpr: ("var", id), ("const", n),
    ("add"|"sub"|"mul"|"div", lhs, rhs), ("neg", arg),
    or ("pow", exponent, arg).  No arithmetic rewriting is assumed.
    """
    if not isinstance(names, dict) or not isinstance(bindings, dict):
        return None
    if len(set(names.values())) != len(names):
        return None
    seen = [0]

    def walk(e, stack):
        seen[0] += 1
        if seen[0] > 16384 or not isinstance(e, (tuple, list)) or not e:
            return None
        op = e[0]
        if op == "var" and len(e) == 2 and type(e[1]) is int:
            v = e[1]
            if v in stack:
                return None
            if v in bindings:
                return walk(bindings[v], stack | {v})
            value = names.get(v)
            return ["source", value] if isinstance(value, str) and value else None
        if op == "const" and len(e) == 2 and type(e[1]) is int:
            return ["const", e[1]]
        if op in ("add", "sub", "mul", "div") and len(e) == 3:
            left, right = walk(e[1], stack), walk(e[2], stack)
            return [op, left, right] if left is not None and right is not None else None
        if op == "neg" and len(e) == 2:
            arg = walk(e[1], stack)
            return [op, arg] if arg is not None else None
        if op == "pow" and len(e) == 3 and type(e[1]) is int:
            arg = walk(e[2], stack)
            return [op, e[1], arg] if arg is not None else None
        return None

    try:
        normalized = walk(expr, set())
    except RecursionError:
        return None
    return json.dumps(normalized, separators=(",", ":"), ensure_ascii=False) if normalized is not None else None


def classify(old_ports, new_ports, old_names, old_bindings, new_names, new_bindings):
    """Return (REVIEW_REQUIRED|UNKNOWN|UNCHANGED, affected origin labels).

    This is a research contract for future generator-emitted metadata, not a
    replacement for the version-1 statement-manifest comparison.
    """
    old_labels = [label for label, _ in old_ports]
    new_labels = [label for label, _ in new_ports]
    if len(set(old_labels)) != len(old_labels) or len(set(new_labels)) != len(new_labels):
        return "UNKNOWN", sorted(set(old_labels) | set(new_labels))
    old = {label: signature(expr, old_names, old_bindings) for label, expr in old_ports}
    new = {label: signature(expr, new_names, new_bindings) for label, expr in new_ports}
    changes = sorted(label for label in old.keys() | new.keys()
                     if label not in old or label not in new
                     or (old[label] is not None and new[label] is not None
                         and old[label] != new[label]))
    unresolved = sorted(label for label in old.keys() | new.keys()
                        if (label in old and old[label] is None)
                        or (label in new and new[label] is None))
    if changes:
        return "REVIEW_REQUIRED", sorted(set(changes) | set(unresolved))
    if unresolved:
        return "UNKNOWN", unresolved
    return "UNCHANGED", []
