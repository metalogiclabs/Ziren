#!/usr/bin/env python3
"""Research-only 2×2 comparator replay on pinned authentic AddSub source.

This script deliberately mutates generated *test inputs*, not a production
chip or the draft PR's source. It does not claim a production miswire.
"""
import argparse
import hashlib
import io
import json
import sys
import tempfile
from pathlib import Path


EXPECTED_ADD_SUB_SHA = "3712e563ce2e71ae3cf285186976355df84633a205db80c28f734c22c0ee1fcb"
EXPECTED_COMPARATOR_BLOB = "2109d1c005211164d7db6998aac4b4187857b052"
CONSTRAINT_END = "\ndef constraints (w : W) : Prop :=\n  constraints_0 w"
INPUT_START = "def inputs (w : W) : List F :=\n  ["


def add_tautology(source):
    assert source.count(CONSTRAINT_END) >= 1
    before, after = source.split(CONSTRAINT_END, 1)
    assert before.rstrip().endswith(") = 0"), "unexpected AddSub constraint tail"
    return before.rstrip() + " ∧\n  (w.v9 - w.v9) = 0\n" + CONSTRAINT_END + after


def swap_input_carriers(source):
    assert source.count(INPUT_START) >= 1
    before, after = source.split(INPUT_START, 1)
    line, rest = after.split("]", 1)
    parts = [part.strip() for part in line.split(",")]
    assert len(parts) == 21
    assert parts[1] == "w.v9" and parts[14] == "w.v14"
    parts[1], parts[14] = parts[14], parts[1]
    return before + INPUT_START + ", ".join(parts) + "]" + rest


def module_report(pin, original, changed):
    with tempfile.TemporaryDirectory(prefix="ziren-addsub-pinning-") as root:
        root = Path(root)
        snapshots = []
        for name, source in (("old", original), ("changed", changed)):
            chip = root / name / "ZirenDet" / "Chips" / "AddSub.lean"
            chip.parent.mkdir(parents=True)
            chip.write_text(source)
            snapshots.append(pin.snapshot(str(chip.parent)))
        output = io.StringIO()
        count = pin.compare(*snapshots, all_info=True, out=output)
        return {"weakening_count": count, "report": output.getvalue().strip()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--comparator-dir", type=Path, required=True)
    args = parser.parse_args()
    sys.path.insert(0, str(args.comparator_dir.resolve()))
    import pin_statements as pin

    comparator = (args.comparator_dir / "pin_statements.py").read_bytes()
    comparator_blob = hashlib.sha1(
        b"blob " + str(len(comparator)).encode() + b"\x00" + comparator
    ).hexdigest()
    assert comparator_blob == EXPECTED_COMPARATOR_BLOB, (
        comparator_blob, EXPECTED_COMPARATOR_BLOB
    )

    data = args.source.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    assert digest == EXPECTED_ADD_SUB_SHA, (digest, EXPECTED_ADD_SUB_SHA)
    source = data.decode("utf-8")
    taut = add_tautology(source)
    swap = swap_input_carriers(source)
    combined = swap_input_carriers(taut)
    result = {
        "source_sha256": digest,
        "comparator_git_blob": comparator_blob,
        "control_unchanged": module_report(pin, source, source),
        "control_tautology_only": module_report(pin, source, taut),
        "swap_only": module_report(pin, source, swap),
        "tautology_plus_swap": module_report(pin, source, combined),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    assert result["control_unchanged"]["weakening_count"] == 0
    assert result["control_tautology_only"]["weakening_count"] == 0
    assert result["swap_only"]["weakening_count"] > 0
    # Characterize the comparator's current fail-open behavior. A repaired
    # comparator should invalidate this last assertion; preserve the baseline.
    assert result["tautology_plus_swap"]["weakening_count"] == 0


if __name__ == "__main__":
    main()
