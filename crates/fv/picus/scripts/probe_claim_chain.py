#!/usr/bin/env python3
"""Bounded Ziren claim-chain mutation probe over authentic generated Lean.

Requires one generated AddSub.lean from a pinned Rust source, the unchanged
v1 statement checker, and the independent v4 source-identity comparator.
This measures two controls' complementarity; it is NOT a Lean proof check.
"""

import argparse
import json
import re
import sys
import tempfile
from pathlib import Path

# In the repository, the v1 statement checker lives beside picus under fv/lean4.
# The fork-only probe uses the original checker; it does not modify it.
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean4" / "check"))

import pin_statements as pin_v1
import port_source_witness as source_v4


REL = ("def rel (ins outs : List F) : Prop :=\n"
       "  ∃ w : W, constraints w ∧ inputs w = ins ∧ outputs w = outs")
DETERMINISTIC_CONCLUSION = "    outputs w = outputs w' := by"
OUTPUT_BINDER = "  (w.v477 - (w.v443 * w.v444)) = 0 ∧\n"
# Genuine active equality for an internal witness field.  In this pinned
# AddSub generation, v308 occurs exactly once and is absent from output ports:
# removing it changes the accepted W-valuations without changing port syntax.
INTERNAL_BINDER = "  (w.v308 - (-1 : F)) = 0 ∧\n"
# An active input-domain condition. In the pinned generator, v408 is set to
# one and state_send[0] is v474 = v6; the range predicate is not an equation
# followed by the output-signature comparator.
FRAME_RANGE = "  ((w.v6 * w.v408)).val ≤ 65535 ∧\n"
CONSTRAINTS_HEADER = "def constraints_0 (w : W) : Prop :=\n"
END_ADD = "\nend AddSub_is_add"


def replace_once(source: str, old: str, new: str) -> str:
    if old not in source:
        raise ValueError(f"authentic generated shape changed: {old[:80]!r}")
    return source.replace(old, new, 1)


def mutations(source: str) -> dict[str, str]:
    # Exact qualification for the deliberately *unobserved* internal field:
    # one declaration and one live equality, no other source occurrence.
    if len(re.findall(r"\bv308\b", source_v4.module_body(
            source, "AddSub_is_add"))) != 2:
        raise ValueError("v308 is no longer a uniquely constrained internal field")
    disconnected = replace_once(source, OUTPUT_BINDER, "")
    disconnected = replace_once(
        disconnected, END_ADD,
        "\ndef disconnected (w : W) : Prop :=\n"
        "  (w.v477 - (w.v443 * w.v444)) = 0\n" + END_ADD)
    return {
        "baseline": source,
        "rel_disconnected": replace_once(
            source, REL,
            REL.replace("constraints w ∧", "True ∧")),
        "theorem_weakened": replace_once(
            source, DETERMINISTIC_CONCLUSION,
            "    True := by"),
        "binder_disconnected": disconnected,
        "internal_constraint_removed": replace_once(source, INTERNAL_BINDER, ""),
        "frame_range_removed": replace_once(source, FRAME_RANGE, ""),
        "vacuous_constraints": replace_once(
            source, CONSTRAINTS_HEADER, CONSTRAINTS_HEADER + "  False ∧\n"),
    }


def module_view(path: Path, namespace: str) -> dict:
    chip, mods, axioms, _header = pin_v1.scan_file(path)
    found = [m for m in mods if m.namespace == namespace]
    if chip != "AddSub" or len(found) != 1:
        raise ValueError(f"unexpected source modules: chip={chip}, matches={len(found)}")
    return {"manifest": pin_v1.summarize(found[0]), "axioms": axioms}


def experiment(path: Path) -> dict:
    source = path.read_text()
    variants = mutations(source)
    # This syntactic intervention has a direct logical consequence, independent
    # of proof automation: constraints_0 is a conjunct of constraints, which is
    # an existential witness requirement of rel; False ∧ ... admits no row.
    vacuous_body = source_v4.module_body(variants["vacuous_constraints"], "AddSub_is_add")
    if (not source_v4.active_constraint_text(vacuous_body).lstrip().startswith("False ∧")
            or "  constraints_0 w ∧" not in vacuous_body
            or "∃ w : W, constraints w ∧" not in vacuous_body):
        raise AssertionError("vacuity witness is no longer on the active rel path")
    results = {}
    with tempfile.TemporaryDirectory(prefix="ziren-claim-chain-") as temp:
        root = Path(temp)
        originals = {}
        for name, content in variants.items():
            target = root / f"{name}.lean"
            target.write_text(content)
            originals[name] = module_view(target, "AddSub_is_add")
        old = originals["baseline"]
        for name, content in variants.items():
            new = originals[name]
            weak, info = pin_v1.compare_module(old["manifest"], new["manifest"])
            new_axioms = sorted(set(new["axioms"]) - set(old["axioms"]))
            source_status, source_ports = source_v4.compare_sources(
                source, content, "AddSub_is_add")
            results[name] = {
                "source": source_status,
                "source_ports": source_ports,
                "v1_weakening": weak,
                "v1_information": info,
                "new_axioms": new_axioms,
            }

    expected = {
        "baseline": ("UNCHANGED", False),
        "rel_disconnected": ("UNCHANGED", True),
        "theorem_weakened": ("UNCHANGED", True),
        "binder_disconnected": ("UNKNOWN", False),
        "internal_constraint_removed": ("UNCHANGED", False),
        "frame_range_removed": ("UNCHANGED", False),
        "vacuous_constraints": ("UNCHANGED", False),
    }
    for name, (source_status, v1_weakening) in expected.items():
        observed = results[name]
        if observed["source"] != source_status or bool(observed["v1_weakening"]) != v1_weakening:
            raise AssertionError(f"{name}: {observed}")
    if results["binder_disconnected"]["source_ports"] != ["state_send[3]"]:
        raise AssertionError(results["binder_disconnected"])
    if not any("definition rel changed" in item for item in
               results["rel_disconnected"]["v1_weakening"]):
        raise AssertionError(results["rel_disconnected"])
    if not any("deterministic: conclusion changed" in item for item in
               results["theorem_weakened"]["v1_weakening"]):
        raise AssertionError(results["theorem_weakened"])
    if not any("constraints changed" in item for item in
               results["binder_disconnected"]["v1_information"]):
        raise AssertionError(results["binder_disconnected"])
    if not any("constraints changed" in item for item in
               results["internal_constraint_removed"]["v1_information"]):
        raise AssertionError(results["internal_constraint_removed"])
    if not any("range facts 25 -> 24" in item for item in
               results["frame_range_removed"]["v1_information"]):
        raise AssertionError(results["frame_range_removed"])
    if not any("constraints changed" in item for item in
               results["vacuous_constraints"]["v1_information"]):
        raise AssertionError(results["vacuous_constraints"])
    if any(case["new_axioms"] for case in results.values()):
        raise AssertionError("unexpected new axiom in text mutation probe")
    return results


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("addsub_lean", type=Path)
    args = ap.parse_args()
    print(json.dumps(experiment(args.addsub_lean), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
