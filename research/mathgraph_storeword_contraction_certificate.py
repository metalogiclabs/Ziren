#!/usr/bin/env python3
"""Source-only certificate for StoreWord witness-field contraction.

This is a syntactic substitution/port theorem certificate, NOT a Lean proof that
the old and new existential relations are equivalent.  In particular, proving
the backward and forward implications requires reasoning about old witnesses.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
for parent in (SCRIPT_DIR / 'ziren-experiment', SCRIPT_DIR / 'crates/fv/lean4/check'):
    if (parent / 'pin_statements.py').exists():
        sys.path.insert(0, str(parent))
        break
from pin_statements import VAR, scan_file, squash

MODULES = ('StoreWord_is_sc', 'StoreWord_is_sw', 'top')
CONTRACTED = (41, 42, 43, 44)
TARGETS = (11, 12, 13, 14)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rewrite(text, mapping):
    def sub(match):
        old_id = int(match.group(2))
        if old_id not in mapping:
            raise ValueError(f'Unmapped field {old_id}')
        return match.group(1) + '.v' + str(mapping[old_id])
    return squash(VAR.sub(sub, text))


def certificate(old_path, new_path):
    old = {m.namespace: m for m in scan_file(old_path)[1]}
    new = {m.namespace: m for m in scan_file(new_path)[1]}
    record = {
        'status': 'SOURCE_SUBSTITUTION_CERTIFIED_NOT_RELATIONAL_PROOF',
        'old_sha256': sha(old_path), 'new_sha256': sha(new_path),
        'contracted_old_fields': dict(zip(map(str, CONTRACTED), TARGETS)),
        'modules': {},
    }
    for name in MODULES:
        a, b = old[name], new[name]
        retained = [(n, doc) for n, doc in a.fields if n not in CONTRACTED]
        assert len(retained) == len(b.fields), (name, 'field-count')
        mapping = {i: j for (i, _), (j, _) in zip(retained, b.fields)}
        mapping.update(zip(CONTRACTED, TARGETS))
        assert len(mapping) == len(a.fields), (name, 'not-all-fields-covered')
        assert len(set(mapping.values())) == len(b.fields), (name, 'lost-other-fields')
        assert all(mapping[n] == t for n, t in zip(CONTRACTED, TARGETS))

        assert len(a.constraint_lines) == len(b.constraint_lines), (name, 'constraint-count')
        for n, (before, after) in enumerate(zip(a.constraint_lines, b.constraint_lines)):
            assert rewrite(before, mapping) == squash(after), (name, 'constraint', n)

        for kind in ('inputs', 'outputs', 'assumed'):
            assert [mapping[n] for n in a.ports[kind]] == b.ports[kind], (name, kind)
        for kind in ('input_origins', 'output_origins'):
            assert a.origins.get(kind) == b.origins.get(kind), (name, kind, 'origin')

        assert a.theorems.keys() == b.theorems.keys(), (name, 'theorem set')
        for kind in a.theorems:
            assert rewrite(a.theorems[kind], mapping) == squash(b.theorems[kind]), (name, kind, 'theorem')

        record['modules'][name] = {
            'old_fields': len(a.fields), 'new_fields': len(b.fields),
            'mapped_constraints': len(a.constraint_lines),
            'ports': {k: len(a.ports[k]) for k in ('inputs', 'outputs', 'assumed')},
            'theorems': sorted(a.theorems),
            'retained_mapping': {str(k): v for k, v in sorted(mapping.items()) if k not in CONTRACTED},
        }
    return record


def negative_controls(old_path, new_path):
    """In-memory mutations: reject a changed constraint and changed output."""
    old = {m.namespace: m for m in scan_file(old_path)[1]}
    new = {m.namespace: m for m in scan_file(new_path)[1]}
    a, b = old['StoreWord_is_sw'], new['StoreWord_is_sw']
    retained = [(n, doc) for n, doc in a.fields if n not in CONTRACTED]
    mapping = {i: j for (i, _), (j, _) in zip(retained, b.fields)}
    mapping.update(zip(CONTRACTED, TARGETS))
    assert rewrite(a.constraint_lines[14], mapping) == squash(b.constraint_lines[14])
    changed = re.sub(r'\bw\.v15\b', 'w.v0', b.constraint_lines[14], count=1)
    assert changed != b.constraint_lines[14]
    changed_constraint_rejected = rewrite(a.constraint_lines[14], mapping) != squash(changed)
    out = list(b.ports['outputs'])
    assert out[5] == 11 and out[6] == 12
    out[5], out[6] = out[6], out[5]
    changed_port_rejected = [mapping[x] for x in a.ports['outputs']] != out
    assert changed_constraint_rejected and changed_port_rejected
    return {'constraint_semantic_mutation_rejected': True, 'output_order_mutation_rejected': True}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--old', type=Path, required=True)
    ap.add_argument('--new', type=Path, required=True)
    args = ap.parse_args()
    result = certificate(args.old, args.new)
    result['negative_controls'] = negative_controls(args.old, args.new)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
