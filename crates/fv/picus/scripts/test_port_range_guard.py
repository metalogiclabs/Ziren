"""Source-native named-port U16 guard controls (bounded; not a kernel proof)."""

import unittest
import os
from pathlib import Path

import port_range_guard as guard


ROOT = Path(os.environ.get(
    "ZIREN_REIFY_SOURCE_ROOT",
    str(Path(__file__).parent / "ziren_replay_artifact_42544409666"),
))
ORIG = ROOT / "generated-r2/ZirenDet/Chips/AddSub.lean"
MUTANT = ROOT / "generated-shard-r2/ZirenDet/Chips/AddSub.lean"
R4 = ROOT / "generated-r4/ZirenDet/Chips/AddSub.lean"


class PortRangeGuardTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = ORIG.read_text(encoding="utf-8")
        cls.mutant = MUTANT.read_text(encoding="utf-8")
        cls.r4 = R4.read_text(encoding="utf-8")

    def test_original_and_benign_reification_enforce_same_shard_bound(self):
        for source in (self.original, self.r4):
            with self.subTest(source=source[:45]):
                result = guard.port_range(source, "AddSub_is_add", "state_recv[0]", "state_send[0]")
                self.assertEqual(result["status"], "QUALIFIED_EXPLICIT_BOUND")
                self.assertEqual(result["maximum"], 65535)

    def test_genuine_rust_mutant_detects_missing_named_port_bound(self):
        result = guard.compare_port_range(
            self.original, self.mutant, "AddSub_is_add", "state_recv[0]", "state_send[0]"
        )
        self.assertEqual(result["status"], "EXPLICIT_BOUND_REMOVED")
        self.assertEqual(result["before_maximum"], 65535)
        self.assertIsNone(result["after_maximum"])

    def test_unbound_port_identity_is_unknown_not_unchanged(self):
        altered = self.original.replace('"state_recv[0]"', '"unidentified_state"', 1)
        result = guard.compare_port_range(
            self.original, altered, "AddSub_is_add", "state_recv[0]", "state_send[0]"
        )
        self.assertEqual(result["status"], "UNKNOWN")

    def test_unforced_gate_is_unknown_not_explicit_bound(self):
        altered = self.original.replace("(w.v408 - (1 : F)) = 0 ∧", "(w.v408 - (0 : F)) = 0 ∧", 1)
        result = guard.port_range(altered, "AddSub_is_add", "state_recv[0]", "state_send[0]")
        self.assertEqual(result["status"], "UNKNOWN")


if __name__ == "__main__":
    unittest.main()
