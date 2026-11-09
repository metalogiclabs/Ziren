"""Bounded named-port range obligations across authentic Ziren reification.

Only an explicit, active range shape is certified. Missing range text is not
proof that no other constraint or chip can restrict the same input.
"""

import re

import port_source_witness as reader


def _parse_ports(body: str, direction: str) -> dict[str, int]:
    origin_name = "input_origins" if direction == "inputs" else "output_origins"
    labels = re.findall(rf'^def {origin_name} : List String := \[([^\n]+)\]$', body, re.M)
    ports = re.findall(rf'^def {direction} \(w : W\) : List F :=\s*\n\s*\[([^\]\n]+)\]$', body, re.M)
    if len(labels) != 1 or len(ports) != 1:
        raise reader.Unwitnessed(f"missing or ambiguous {direction}")
    names = re.findall(r'"([^"\n]+)"', labels[0])
    variables = [v.strip() for v in ports[0].split(",")]
    if len(names) != len(variables) or len(names) != len(set(names)):
        raise reader.Unwitnessed(f"ambiguous {direction} labels")
    if any(not re.fullmatch(r'w\.v\d+', v) for v in variables):
        raise reader.Unwitnessed(f"unsupported {direction} value")
    return dict(zip(names, (int(v[3:]) for v in variables)))


def _unit_gates(active: str) -> set[int]:
    return {int(i) for i in re.findall(r'^\s*\(w\.v(\d+) - \(1 : F\)\) = 0(?: ∧)?$', active, re.M)}


def _frame_echo(port_id: int, frame_id: int, active: str, gates: set[int]) -> bool:
    if port_id == frame_id:
        return True
    matches = re.findall(rf'^\s*\(w\.v{port_id} - (.+)\) = 0(?: ∧)?$', active, re.M)
    if len(matches) != 1:
        return False
    m = re.fullmatch(rf'\(w\.v{frame_id} \* w\.v(\d+)\)', matches[0])
    return bool(m and int(m[1]) in gates)


def port_range(source: str, module: str, incoming: str, outgoing: str) -> dict:
    try:
        body = reader.module_body(source, module)
        active = reader.active_constraint_text(body)
        ins = _parse_ports(body, "inputs")
        outs = _parse_ports(body, "outputs")
        annotations = re.findall(r'/-- `([^`]+)` -/\s*\n\s*v(\d+) : F', body)
        frame_fields = [int(i) for name, i in annotations if name == "frame[0]"]
        if (len(frame_fields) != 1 or incoming not in ins or outgoing not in outs
                or len(annotations) != len(set(annotations))):
            raise reader.Unwitnessed("unqualified frame or port source labels")
        frame = frame_fields[0]
        gates = _unit_gates(active)
        # The independent source-origin tracer disallows a naked output
        # equality being mistaken for an identity across generated columns.
        source_out = reader.source_witnesses(source, module).get(outgoing)
        if (source_out is None or source_out.expression != "@frame[0]"
                or not _frame_echo(ins[incoming], frame, active, gates)
                or not _frame_echo(outs[outgoing], frame, active, gates)):
            raise reader.Unwitnessed("named ports do not both expose frame[0]")
        caps = []
        for raw in active.splitlines():
            term = raw.strip().removesuffix(" ∧").strip()
            if ".val ≤" not in term or f"w.v{frame}" not in term:
                continue
            direct = re.fullmatch(rf'\(w\.v{frame}\)\.val ≤ (\d+)', term)
            gated = re.fullmatch(rf'\(\(w\.v{frame} \* w\.v(\d+)\)\)\.val ≤ (\d+)', term)
            if direct:
                caps.append(int(direct[1]))
            elif gated and int(gated[1]) in gates:
                caps.append(int(gated[2]))
            else:
                raise reader.Unwitnessed("unsupported or unforced range involving frame[0]")
        if caps:
            return {"status": "QUALIFIED_EXPLICIT_BOUND", "maximum": min(caps)}
        return {"status": "NO_EXPLICIT_BOUND_FOUND", "maximum": None}
    except reader.Unwitnessed as exc:
        return {"status": "UNKNOWN", "reason": str(exc)}


def compare_port_range(before: str, after: str, module: str, incoming: str, outgoing: str) -> dict:
    b = port_range(before, module, incoming, outgoing)
    a = port_range(after, module, incoming, outgoing)
    if b["status"] == "QUALIFIED_EXPLICIT_BOUND" and a["status"] == "NO_EXPLICIT_BOUND_FOUND":
        return {"status": "EXPLICIT_BOUND_REMOVED", "before_maximum": b["maximum"],
                "after_maximum": None}
    if b["status"] == a["status"] == "QUALIFIED_EXPLICIT_BOUND" and b["maximum"] == a["maximum"]:
        return {"status": "UNCHANGED_EXPLICIT_BOUND", "maximum": b["maximum"]}
    return {"status": "UNKNOWN", "before": b, "after": a}
