"""Executable red/green controls for the bounded Lean source-fidelity comparator."""

import unittest

import port_source_witness as witness


BASE = """
namespace AddSub_is_add
structure W where
  /-- `frame[0]` -/
  v1 : F
  v101 : F
  v102 : F
def output_origins : List String := ["state_send[1]", "state_send[3]"]
def outputs (w : W) : List F :=
  [w.v101, w.v102]
def constraints (w : W) : Prop :=
  (w.v101 - (w.v1 + (4 : F))) = 0 ∧
  (w.v102 - (w.v1 + (5 : F))) = 0
end AddSub_is_add
"""


class SourceFidelityComparisonTest(unittest.TestCase):
    def test_comparator_exists(self):
        self.assertTrue(hasattr(witness, "compare_sources"), "source comparator is missing")

    def test_identical_qualified_source_is_unchanged(self):
        self.assertEqual(witness.compare_sources(BASE, BASE, "AddSub_is_add"), ("UNCHANGED", []))

    def test_direct_source_column_survives_real_index_reassignment(self):
        direct = BASE.replace('"state_send[1]", "state_send[3]"', '"state_send[0]"')
        direct = direct.replace('[w.v101, w.v102]', '[w.v1]')
        self.assertEqual(witness.compare_sources(direct, direct.replace('v1', 'v2'), "AddSub_is_add"),
                         ("UNCHANGED", []))

    def test_direct_source_column_rebind_requires_review(self):
        direct = BASE.replace('"state_send[1]", "state_send[3]"', '"state_send[0]"')
        direct = direct.replace('[w.v101, w.v102]', '[w.v1]')
        changed = direct.replace('`frame[0]`', '`frame[1]`')
        self.assertEqual(witness.compare_sources(direct, changed, "AddSub_is_add"),
                         ("REVIEW_REQUIRED", ["state_send[0]"]))

    def test_nested_emitted_equality_alias_is_source_preserving(self):
        nested = BASE.replace('  (w.v101 - (w.v1 + (4 : F))) = 0 ∧\n',
                              '  (w.v201 - (w.v1 + (4 : F))) = 0 ∧\n'
                              '  (w.v101 - w.v201) = 0 ∧\n')
        self.assertEqual(witness.compare_sources(BASE, nested, "AddSub_is_add"),
                         ("UNCHANGED", []))

    def test_nested_equality_rebind_is_not_hidden_by_alias(self):
        nested = BASE.replace('  (w.v101 - (w.v1 + (4 : F))) = 0 ∧\n',
                              '  (w.v201 - (w.v1 + (6 : F))) = 0 ∧\n'
                              '  (w.v101 - w.v201) = 0 ∧\n')
        self.assertEqual(witness.compare_sources(BASE, nested, "AddSub_is_add"),
                         ("REVIEW_REQUIRED", ["state_send[1]"]))

    def test_nested_equality_missing_intermediate_is_unknown(self):
        missing = BASE.replace('  (w.v101 - (w.v1 + (4 : F))) = 0 ∧\n',
                               '  (w.v101 - w.v201) = 0 ∧\n')
        self.assertEqual(witness.compare_sources(BASE, missing, "AddSub_is_add"),
                         ("UNKNOWN", ["<unqualified interface>"]))

    def test_nested_equality_cycle_is_unknown(self):
        cyclic = BASE.replace('  (w.v101 - (w.v1 + (4 : F))) = 0 ∧\n',
                              '  (w.v101 - w.v201) = 0 ∧\n'
                              '  (w.v201 - w.v101) = 0 ∧\n')
        self.assertEqual(witness.compare_sources(BASE, cyclic, "AddSub_is_add"),
                         ("UNKNOWN", ["<unqualified interface>"]))

    def test_witnessed_multiplicity_one_is_a_harmless_reification(self):
        gated = BASE.replace('  (w.v101 - (w.v1 + (4 : F))) = 0 ∧\n',
                             '  (w.v201 - (1 : F)) = 0 ∧\n'
                             '  (w.v101 - ((w.v1 + (4 : F)) * w.v201)) = 0 ∧\n')
        self.assertEqual(witness.compare_sources(BASE, gated, "AddSub_is_add"),
                         ("UNCHANGED", []))

    def test_witnessed_multiplicity_two_remains_a_real_change(self):
        gated = BASE.replace('  (w.v101 - (w.v1 + (4 : F))) = 0 ∧\n',
                             '  (w.v201 - (2 : F)) = 0 ∧\n'
                             '  (w.v101 - ((w.v1 + (4 : F)) * w.v201)) = 0 ∧\n')
        self.assertEqual(witness.compare_sources(BASE, gated, "AddSub_is_add"),
                         ("REVIEW_REQUIRED", ["state_send[1]"]))

    def test_multiplicative_identity_without_emitted_equality_is_unknown(self):
        unbound = BASE.replace('  (w.v101 - (w.v1 + (4 : F))) = 0 ∧\n',
                               '  (w.v101 - ((w.v1 + (4 : F)) * w.v201)) = 0 ∧\n')
        self.assertEqual(witness.compare_sources(BASE, unbound, "AddSub_is_add"),
                         ("UNKNOWN", ["<unqualified interface>"]))

    def test_multiplicative_identity_cannot_hide_inner_semantic_change(self):
        changed = BASE.replace('  (w.v101 - (w.v1 + (4 : F))) = 0 ∧\n',
                               '  (w.v201 - (1 : F)) = 0 ∧\n'
                               '  (w.v101 - ((w.v1 + (6 : F)) * w.v201)) = 0 ∧\n')
        self.assertEqual(witness.compare_sources(BASE, changed, "AddSub_is_add"),
                         ("REVIEW_REQUIRED", ["state_send[1]"]))

    def test_unbalanced_emitted_intermediate_is_unknown(self):
        malformed = BASE.replace('  (w.v101 - (w.v1 + (4 : F))) = 0 ∧\n',
                                 '  (w.v201 - (w.v1 + (4 : F))) + (3 : F) = 0 ∧\n'
                                 '  (w.v101 - w.v201) = 0 ∧\n')
        self.assertEqual(witness.compare_sources(BASE, malformed, "AddSub_is_add"),
                         ("UNKNOWN", ["<unqualified interface>"]))

    def test_benign_field_insertion_does_not_trigger_review(self):
        shifted = BASE.replace("v1", "v2")
        self.assertEqual(witness.compare_sources(BASE, shifted, "AddSub_is_add"), ("UNCHANGED", []))

    def test_same_base_derived_port_rebind_requires_review(self):
        rebound = BASE.replace("(4 : F)", "__OLD__").replace("(5 : F)", "(4 : F)").replace("__OLD__", "(5 : F)")
        self.assertEqual(witness.compare_sources(BASE, rebound, "AddSub_is_add"),
                         ("REVIEW_REQUIRED", ["state_send[1]", "state_send[3]"]))

    def test_constrained_to_free_port_fails_closed(self):
        missing = BASE.replace("  (w.v102 - (w.v1 + (5 : F))) = 0\n", "")
        self.assertEqual(witness.compare_sources(BASE, missing, "AddSub_is_add"),
                         ("UNKNOWN", ["state_send[3]"]))

    def test_duplicate_output_origin_fails_closed(self):
        malformed = BASE.replace('"state_send[3]"', '"state_send[1]"')
        self.assertEqual(witness.compare_sources(BASE, malformed, "AddSub_is_add"),
                         ("UNKNOWN", ["<unqualified interface>"]))


if __name__ == "__main__":
    unittest.main()
