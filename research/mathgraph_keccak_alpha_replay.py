#!/usr/bin/env python3
"""Fail-closed Keccak proof-recipe transport experiment (not a Lean kernel check)."""
import contextlib
import hashlib
import importlib.machinery
import io
import json
import os
import pathlib
import re
import sys

here = pathlib.Path(__file__).resolve().parent
candidate_checkers = (
    pathlib.Path(os.environ.get('MATHGRAPH_CHECKER_DIR', '/nonexistent')),
    here / 'crates/fv/lean4/check',
    here / 'ziren-pr575/crates/fv/lean4/check',
)
sys.path.insert(0, str(next(d for d in candidate_checkers
                            if (d / 'pin_statements.py').is_file())))
import pin_statements as pin


def module(path):
    chip, modules, _, _ = pin.scan_file(pathlib.Path(path))
    assert chip == 'KeccakSponge', chip
    found = [m for m in modules if m.namespace == 'KeccakSponge']
    assert len(found) == 1, [m.namespace for m in modules]
    return found[0]


def certify(oldpath, newpath):
    old, new = module(oldpath), module(newpath)
    oldnames, newnames = pin.column_names(old.fields), pin.column_names(new.fields)
    assert len(set(oldnames.values())) == len(oldnames)
    assert len(set(newnames.values())) == len(newnames)
    assert set(oldnames.values()) == set(newnames.values()), 'Witness fields changed'
    reverse = {name: idx for idx, name in newnames.items()}
    renaming = {idx: reverse[name] for idx, name in oldnames.items()}
    assert len(set(renaming.values())) == len(renaming) == len(new.fields)

    a = [pin.squash(pin.canonical(s, oldnames)) for s in old.constraint_lines]
    b = [pin.squash(pin.canonical(s, newnames)) for s in new.constraint_lines]
    assert a == b, 'Canonical constraints differ'

    def ports(mod, names, kind):
        origin_type = {'inputs': 'input_origins', 'outputs': 'output_origins'}.get(kind, '')
        names_by_origin = mod.origins.get(origin_type, [])
        idxs = mod.ports[kind]
        assert len(names_by_origin) == len(idxs) if origin_type else not idxs
        return [(label, names[idx]) for label, idx in zip(names_by_origin, idxs)]

    for kind in ('inputs', 'outputs', 'assumed'):
        assert ports(old, oldnames, kind) == ports(new, newnames, kind), kind
    oldsummary, newsummary = pin.summarize(old), pin.summarize(new)
    assert oldsummary['hashes'] == newsummary['hashes'], 'Tracked statement/constraint hashes differ'
    assert oldsummary['port_sources'] == newsummary['port_sources'], 'Constraint source bindings differ'
    assert oldsummary['theorems'] == newsummary['theorems'], 'Determinism claims differ'

    pairs = [[a, b] for a, b in sorted(renaming.items())]
    return {
        'verification_boundary': 'Python AST/text canonical comparison; Lean proof transport not checked',
        'old_source_sha256': hashlib.sha256(pathlib.Path(oldpath).read_bytes()).hexdigest(),
        'new_source_sha256': hashlib.sha256(pathlib.Path(newpath).read_bytes()).hexdigest(),
        'witness_bijection_fields': len(renaming),
        'changed_numeric_field_ids': sum(a != b for a, b in renaming.items()),
        'canonical_constraint_count': len(a),
        'canonical_constraint_sha256': hashlib.sha256(
            json.dumps(a, ensure_ascii=False, separators=(',', ':')).encode()).hexdigest(),
        'complete_alpha_equivalence': True,
        'ports_and_declarations_match': True,
        'old_to_new_column_map_sha256': hashlib.sha256(json.dumps(pairs).encode()).hexdigest(),
        'example_mappings': [[idx, renaming[idx]] for idx in (0, 23, 125, 224, 2635, 6930)
                             if idx in renaming],
    }


def replay(oldpath, newpath, generator_path, outpath):
    report = certify(oldpath, newpath)
    old_columns = pin.column_names(module(oldpath).fields)
    new_columns = pin.column_names(module(newpath).fields)
    new_by_name = {name: idx for idx, name in new_columns.items()}
    mapping = {idx: new_by_name[name] for idx, name in old_columns.items()}

    generator_path = pathlib.Path(generator_path)
    sys.path.insert(0, str(generator_path.parent))
    generator = importlib.machinery.SourceFileLoader(
        'ziren_archived_keccak_recipe', str(generator_path)).load_module()
    mapped = lambda old: mapping[old]
    generator.FLAG = lambda i: mapped(i)
    generator.A = lambda y, x, l: mapped(125 + 20 * y + 4 * x + l)
    generator.C = lambda x, z: mapped(225 + 64 * x + z)
    generator.CP = lambda x, z: mapped(545 + 64 * x + z)
    generator.AP = lambda y, x, z: mapped(865 + 320 * y + 64 * x + z)
    generator.APP = lambda y, x, l: mapped(2465 + 20 * y + 4 * x + l)
    generator.B00 = lambda z: mapped(2565 + z)
    generator.APPP = lambda l: mapped(2629 + l)

    saved_args = sys.argv
    sys.argv = [str(generator_path), str(newpath), str(outpath)]
    result = io.StringIO()
    try:
        with contextlib.redirect_stdout(result):
            generator.main()
    finally:
        sys.argv = saved_args
    data = pathlib.Path(outpath).read_bytes()
    assert b'theorem gadget_det' in data
    assert not re.search(rb'\b(?:sorry|admit)\b', data)
    report.update({
        'generator_stdout': result.getvalue().strip(),
        'generated_snippet_bytes': len(data),
        'generated_snippet_sha256': hashlib.sha256(data).hexdigest(),
        'no_sorry_or_admit_in_snippet': True,
        'lean_kernel_check': 'NOT RUN',
    })
    return report


if __name__ == '__main__':
    if len(sys.argv) == 3:
        report = certify(sys.argv[1], sys.argv[2])
    elif len(sys.argv) == 5:
        report = replay(*sys.argv[1:5])
    else:
        sys.exit('usage: alpha-replay.py OLD NEW [GENERATOR SNIPPET_OUT]')
    print(json.dumps(report, indent=2, sort_keys=True))
