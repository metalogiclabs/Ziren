"""Behavioral controls for the bounded authentic AddSub witness experiment.

Each test guards an observable semantic failure: a falsely admitted row,
an overlooked constraint, a silently accepted unsupported expression, or
an incorrect input/output port projection.
"""

import os
import unittest
from pathlib import Path

import addsub_witness_probe as probe


SOURCE = Path(os.environ.get(
    "ZIREN_ADD_SUB_LEAN",
    "/tmp/ziren_reify_sweep_current/generated-r2/ZirenDet/Chips/AddSub.lean",
))
RANGE = "  ((w.v6 * w.v408)).val ≤ 65535 ∧\n"
HEADER = "def constraints_0 (w : W) : Prop :=\n"


class AddSubWitnessProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = SOURCE.read_text(encoding="utf-8")

    def test_real_witness_satisfies_all_emitted_conjuncts(self):
        result = probe.evaluate(self.original, frame0=0)
        self.assertGreater(result["constraint_count"], 200)
        self.assertEqual(result["failed"], [])
        self.assertEqual(result["inputs"][21], 0)  # state_recv[0]
        self.assertEqual(result["outputs"][0], 0)  # state_send[0]

    def test_frame_overflow_is_rejected_only_by_explicit_domain_fact(self):
        result = probe.evaluate(self.original, frame0=65536)
        self.assertEqual(result["failed"], ["((w.v6 * w.v408)).val ≤ 65535"])
        self.assertEqual(result["inputs"][21], 65536)
        self.assertEqual(result["outputs"][0], 65536)
        self.assertEqual(result["assignments"]["v408"], 1)
        self.assertEqual(result["assignments"]["v452"], 1)

    def test_removed_range_admits_external_row_original_excludes(self):
        self.assertEqual(self.original.count(RANGE), 1)
        changed = self.original.replace(RANGE, "", 1)
        result = probe.evaluate(changed, frame0=65536)
        self.assertEqual(result["failed"], [])
        self.assertEqual(result["inputs"][21], 65536)
        self.assertEqual(result["outputs"][0], 65536)
        self.assertEqual(result["constraint_count"], probe.evaluate(self.original, 0)["constraint_count"] - 1)

    def test_active_false_is_rejected_for_real_witness(self):
        self.assertGreaterEqual(self.original.count(HEADER), 1)
        changed = self.original.replace(HEADER, HEADER + "  False ∧\n", 1)
        result = probe.evaluate(changed, frame0=0)
        self.assertEqual(result["failed"], ["False"])

    def test_unrecognized_active_constraint_fails_closed(self):
        changed = self.original.replace(HEADER, HEADER + "  w.v6 = w.v7 ∧\n", 1)
        with self.assertRaises(probe.Unqualified):
            probe.evaluate(changed, frame0=0)

    def test_relabelled_external_input_cannot_claim_same_contract(self):
        label_pair = '"state_recv[0]", "state_recv[1]"'
        self.assertGreaterEqual(self.original.count(label_pair), 1)
        changed = self.original.replace(label_pair, '"state_recv_missing", "state_recv[1]"', 1)
        with self.assertRaises(probe.Unqualified):
            probe.evaluate(changed, frame0=0)

    def test_renumbered_derived_fields_preserve_named_external_paths(self):
        marker = "\nend AddSub_is_add"
        prefix, suffix = self.original.split(marker, 1)
        self.assertIn("v493 : F", prefix)
        renamed = prefix.replace("v493", "v993").replace("v474", "v994")
        changed = renamed + marker + suffix
        result = probe.evaluate(changed, frame0=65536)
        self.assertEqual(result["inputs"][21], 65536)
        self.assertEqual(result["outputs"][0], 65536)
        self.assertEqual(result["failed"], ["((w.v6 * w.v408)).val ≤ 65535"])

    @unittest.skipUnless(os.environ.get("ZIREN_SHARD_ADD_SUB_LEAN"), "authentic Rust mutant required")
    def test_actual_rust_omission_admits_shard_65536(self):
        generated = Path(os.environ["ZIREN_SHARD_ADD_SUB_LEAN"]).read_text(encoding="utf-8")
        result = probe.evaluate(generated, frame0=65536)
        self.assertEqual(result["failed"], [])
        self.assertEqual(result["constraint_count"], 235)
        self.assertEqual(result["inputs"][21], 65536)
        self.assertEqual(result["outputs"][0], 65536)


if __name__ == "__main__":
    unittest.main()
