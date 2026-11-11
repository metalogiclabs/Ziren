#!/usr/bin/env python3
"""Source-only Branch/Jump four-column contraction certificate.

Neither the source substitution nor removal of tautological rows establishes
the old-to-new existential implication: gated aliases require proof.
"""
import argparse
import difflib
import hashlib
import json
import sys
from pathlib import Path

for parent in (Path(__file__).resolve().parent / 'ziren-experiment',
               Path(__file__).resolve().parent / 'crates/fv/lean4/check'):
    if (parent / 'pin_statements.py').exists():
        sys.path.insert(0, str(parent))
        break
from pin_statements import VAR, scan_file, squash


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tr(s, mapping):
    return squash(VAR.sub(lambda m: m.group(1)+'.v'+str(mapping[int(m.group(2))]),s)).removesuffix(' ∧')


def qualify(a, b):
    removed = [i for i, name in a.fields if name and name.startswith('target_add_')]
    targets = [i for i, name in a.fields if name and name.startswith('next_next_pc_') and 'range' not in name]
    assert len(removed) == len(targets) == 4
    kept = [(i, name) for i, name in a.fields if i not in removed]
    assert len(kept) == len(b.fields)
    mapping = {i:j for (i,_), (j,_) in zip(kept, b.fields)}
    assert len(set(mapping.values())) == len(b.fields)
    mapping.update({i:mapping[j] for i,j in zip(removed,targets)})

    before = [tr(s, mapping) for s in a.constraint_lines]
    after = [squash(s).removesuffix(' ∧') for s in b.constraint_lines]
    operations = difflib.SequenceMatcher(a=before,b=after,autojunk=False).get_opcodes()
    deleted = []
    for tag, i, j, k, l in operations:
        assert tag in ('equal', 'delete'), (a.namespace,tag,i,j,k,l)
        if tag == 'delete':
            assert k == l
            deleted.extend((n, before[n]) for n in range(i, j))
    assert len(deleted) == 4
    for n, s in deleted:
        assert s.endswith(' = 0'),(a.namespace,n,s)
        # This precisely tests whether an old target/next-PC equality becomes
        # an identity; it does not discard arbitrary constraints.
        assert any(f'(w.v{mapping[t]} - w.v{mapping[t]})' in s for t in targets), (a.namespace,n,s)

    assert len(before)-len(deleted)==len(after)
    assert a.theorems.keys()==b.theorems.keys()
    assert all(tr(a.theorems[k],mapping)==squash(b.theorems[k]) for k in a.theorems)
    assert all([mapping[i] for i in a.ports[k]]==b.ports[k] for k in ('inputs','outputs','assumed'))
    assert a.origins == b.origins

    return {
        'fields_old_new':[len(a.fields),len(b.fields)],
        'constraints_old_new':[len(before),len(after)],
        'constraints_exact_after_contraction_and_tautology_removal':len(after),
        'dropped_identity_constraint_indices':[i for i,_ in deleted],
        'target_alias_map':{str(i):mapping[i] for i in removed},
        'port_counts':{k:len(a.ports[k]) for k in ('inputs','outputs','assumed')},
        'theorems':sorted(a.theorems),
    }


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--old',type=Path,required=True)
    ap.add_argument('--new',type=Path,required=True)
    args=ap.parse_args()
    assert args.old.stem == args.new.stem in ('Branch','Jump')
    old={m.namespace:m for m in scan_file(args.old)[1]}
    new={m.namespace:m for m in scan_file(args.new)[1]}
    assert old.keys() == new.keys()
    found={}
    for name,a in old.items():
        if any(doc and doc.startswith('target_add_') for _,doc in a.fields):
            found[name]=qualify(a,new[name])
    assert len(found)==(7 if args.old.stem=='Branch' else 2)
    result={
        'status':'SOURCE_SUBSTITUTION_CERTIFIED_NOT_EXISTENTIAL_EQUIVALENCE',
        'chip':args.old.stem,
        'old_sha256':sha(args.old),'new_sha256':sha(args.new),
        'modules':found,
        'total_constraints_matched':sum(r['constraints_exact_after_contraction_and_tautology_removal'] for r in found.values()),
        'removed_tautological_constraints':4*len(found),
    }
    print(json.dumps(result,sort_keys=True,indent=2))


if __name__=='__main__':main()
