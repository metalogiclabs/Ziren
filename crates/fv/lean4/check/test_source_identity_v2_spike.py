#!/usr/bin/env python3
"""Bounded design tests for source-qualified port identities (NOT a production guard).

These terms mirror the PicusExpr tree available at Emitter::bind_port.  The
source-name maps and reification bindings are explicit fixture inputs, not
independently recovered from archived Ziren chip sources.
"""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from source_identity_v2_spike import (
    anchored_signature, classify, classify_anchored, pair_ports, signature,
    stable_names_from_ranges,
)


def var(n):
    return ("var", n)


def add(a, b):
    return ("add", a, b)


def const(n):
    return ("const", n)


class SourceIdentitySpikeTest(unittest.TestCase):
    def test_derived_port_requires_equality_in_emitted_constraints(self):
        # PicusConstraint::new_equality(v, expr) emits Eq(Sub(v, expr)).
        # Producer metadata can say v101 originated from public[0]+4 even
        # after that actual equality is removed from the module.
        source = add(var(0), const(4))
        bindings = {101: source}
        eq = ("eq", ("sub", var(101), source))
        self.assertEqual(
            anchored_signature(var(101), {0: "public[0]"}, bindings, [eq]),
            signature(var(101), {0: "public[0]"}, bindings),
        )
        self.assertIsNone(anchored_signature(var(101), {0: "public[0]"}, bindings, []))
        self.assertEqual(
            classify_anchored(
                [("send[0]", var(101))], [("send[0]", var(101))],
                {0: "public[0]"}, bindings, [eq],
                {0: "public[0]"}, bindings, [],
            ),
            ("UNKNOWN", ["send[0]"]),
        )

    def test_nested_reification_requires_every_observed_equality(self):
        first = add(var(0), const(4))
        second = ("mul", var(101), const(2))
        bindings = {101: first, 102: second}
        e1 = ("eq", ("sub", var(101), first))
        e2 = ("eq", ("sub", var(102), second))
        names = {0: "public[0]"}
        self.assertIsNotNone(anchored_signature(var(102), names, bindings, [e1, e2]))
        self.assertIsNone(anchored_signature(var(102), names, bindings, [e2]))
        self.assertEqual(anchored_signature(var(0), names, {}, []), signature(var(0), names, {}))

    def test_wrong_binding_equality_is_not_provenance(self):
        expected = add(var(0), const(4))
        wrong = add(var(0), const(5))
        bindings = {101: expected}
        self.assertIsNone(anchored_signature(
            var(101), {0: "state[0]"}, bindings,
            [("eq", ("sub", var(101), wrong))],
        ))

    def test_post_extraction_port_mutation_requires_new_origins(self):
        # `build_top_module` currently clears/rebuilds the top module's ports
        # *after* `extract_module` stores PORT_ORIGINS.  The old v1 scanner
        # silently falls back when these lengths disagree; v2 must not.
        self.assertIsNone(pair_ports([var(0), var(1)], ["selector.add"]))
        old = pair_ports([var(0)], ["selector.add"])
        new = pair_ports([var(0), var(1)], ["selector.add"])
        self.assertEqual(classify_anchored(old, new, {0: "selector[0]"}, {}, [],
                                           {0: "selector[0]", 1: "selector[1]"}, {}, []),
                         ("UNKNOWN", ["<unqualified interface>"]))

    def test_field_relative_names_survive_main_column_insertion(self):
        # PicusInfo.col_to_name uses absolute suffixes (public_0 -> public_1),
        # whereas name_to_colrange can recover source field + local offset.
        old = stable_names_from_ranges({"public": (0, 1)})
        new = stable_names_from_ranges({"unused": (0, 1), "public": (1, 2)})
        self.assertEqual(old, {0: "public[0]"})
        self.assertEqual(new, {0: "unused[0]", 1: "public[0]"})
        self.assertEqual(signature(var(0), old, {}), signature(var(1), new, {}))

    def test_overlapping_source_field_ranges_are_unqualified(self):
        self.assertIsNone(stable_names_from_ranges({"state": (0, 2), "other": (1, 3)}))

    def test_missing_source_field_map_is_unknown_instead_of_crashing(self):
        self.assertIsNone(stable_names_from_ranges(None))
        self.assertIsNone(signature(var(0), None, {}))
        status, affected = classify([("send[0]", var(0))], [("send[0]", var(1))],
                                    None, {}, {1: "public[0]"}, {})
        self.assertEqual((status, affected), ("UNKNOWN", ["send[0]"]))

    def test_expands_reified_temporaries_with_stable_names(self):
        # The first extraction calls the temporary v101; the second v203.
        a = signature(var(101), {0: "public_0"}, {101: add(var(0), const(4))})
        b = signature(var(203), {12: "public_0"}, {203: add(var(12), const(4))})
        self.assertEqual(a, b)
        self.assertEqual(a, '["add",["source","public_0"],["const",4]]')

    def test_distinguishes_same_base_output_swap(self):
        names = {0: "public_0"}
        old = [("send[0]", var(101)), ("send[1]", var(102))]
        new = [("send[0]", var(202)), ("send[1]", var(201))]
        bindings1 = {101: add(var(0), const(4)), 102: add(var(0), const(5))}
        bindings2 = {201: add(var(0), const(4)), 202: add(var(0), const(5))}
        status, changes = classify(old, new, names, bindings1, names, bindings2)
        self.assertEqual(status, "REVIEW_REQUIRED")
        self.assertEqual(changes, ["send[0]", "send[1]"])

    def test_detects_move_to_unresolved_free_output(self):
        old = [("send[0]", var(101))]
        new = [("send[0]", var(202))]
        status, changes = classify(old, new, {0: "public_0"},
                                   {101: add(var(0), const(4))}, {0: "public_0"}, {})
        self.assertEqual(status, "UNKNOWN")
        self.assertEqual(changes, ["send[0]"])

    def test_ignores_an_unrelated_derived_column_insertion(self):
        old = [("send[0]", var(101))]
        new = [("send[0]", var(405))]
        status, changes = classify(old, new, {0: "public_0"},
                                   {101: add(var(0), const(4))}, {0: "public_0"},
                                   {405: add(var(0), const(4))})
        self.assertEqual(status, "UNCHANGED")
        self.assertEqual(changes, [])

    def test_fails_closed_on_legacy_or_cyclic_evidence(self):
        source = [("send[0]", var(101))]
        legacy, bad = classify(source, source, {0: "public_0"}, {}, {0: "public_0"}, {})
        self.assertEqual((legacy, bad), ("UNKNOWN", ["send[0]"]))
        cycle = signature(var(101), {0: "public_0"}, {101: var(102), 102: var(101)})
        self.assertIsNone(cycle)

    def test_duplicate_source_names_do_not_prove_equivalence(self):
        # If two different original variables have one name, source qualification
        # itself is lossy and must not certify an unchanged contract.
        original = [("send[0]", var(1))]
        moved = [("send[0]", var(2))]
        status, _ = classify(original, moved, {1: "shared", 2: "shared"}, {},
                             {1: "shared", 2: "shared"}, {})
        self.assertEqual(status, "UNKNOWN")

    def test_known_change_does_not_hide_an_unresolved_port(self):
        original = [("send[0]", var(101)), ("send[1]", var(102))]
        changed = [("send[0]", var(201)), ("send[1]", var(202))]
        status, affected = classify(
            original, changed, {0: "public_0"},
            {101: add(var(0), const(4)), 102: add(var(0), const(6))},
            {0: "public_0"}, {201: add(var(0), const(5))},
        )
        self.assertEqual(status, "REVIEW_REQUIRED")
        self.assertEqual(affected, ["send[0]", "send[1]"])


if __name__ == "__main__":
    unittest.main()
