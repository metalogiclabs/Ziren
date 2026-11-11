#!/usr/bin/env python3
"""Source-parsed finite-field audit of archived/current SysLinux witness rows.

Evaluate every generated Lean constraint directly from exact source, including
field arithmetic, `.val` bounds, and Boolean equivalences. This is a Python
replay of the *full* relation, not a Lean kernel proof. It demonstrates the
old and new source admit different outputs for the same external inputs, and
records source hashes and the exact witness assignments. It does not prove
that these rows are reachable in a complete VM execution.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

for search_dir in (
    Path(__file__).resolve().parent / 'ziren-experiment',
    Path(__file__).resolve().parent.parent / 'crates/fv/lean4/check',
):
    if (search_dir / 'pin_statements.py').is_file():
        sys.path.insert(0, str(search_dir))
        break
from pin_statements import scan_file

P = 2130706433


class F(int):
    def __new__(cls, value):
        return super().__new__(cls, int(value) % P)

    def __add__(self, other):
        return F(int(self) + int(other))

    __radd__ = __add__

    def __sub__(self, other):
        return F(int(self) - int(other))

    def __rsub__(self, other):
        return F(int(other) - int(self))

    def __mul__(self, other):
        return F(int(self) * int(other))

    __rmul__ = __mul__

    @property
    def val(self):
        return int(self)


def inv(number):
    return F(pow(int(number), -1, P))


def balanced(expr):
    """Remove the single outer connective paren split across an iff row."""
    expr = expr.strip()
    while expr.count('(') > expr.count(')'):
        assert expr.startswith('('), expr
        expr = expr[1:]
    while expr.count(')') > expr.count('('):
        assert expr.endswith(')'), expr
        expr = expr[:-1]
    return expr


def parse_expr(source):
    expr = source.strip()
    expr = re.sub(r'\(\((\d+) : F\)⁻¹\)', lambda m: f'inv({m[1]})', expr)
    expr = re.sub(r'\((\d+) : F\)', lambda m: f'F({m[1]})', expr)
    expr = re.sub(r'w\.v(\d+)', lambda m: f'v[{m[1]}]', expr)
    return expr


def check_constraints(mod, v):
    scope = {'v': v, 'F': F, 'inv': inv}
    failures = []
    for idx, raw in enumerate(mod.constraint_lines):
        row = parse_expr(raw.strip().removesuffix('∧').strip())
        if '= 0 ↔' in row:
            lhs, rhs = row.split('= 0 ↔', 1)
            left = bool(eval(balanced(lhs), {'__builtins__': {}}, scope) == 0)
            right = bool(eval(balanced(rhs), {'__builtins__': {}}, scope))
            result = left == right
        elif '.val ≤' in row:
            lhs, rhs = row.split('≤', 1)
            result = eval(lhs, {'__builtins__': {}}, scope) <= int(rhs)
        elif '= 0' in row:
            lhs = row.removesuffix('= 0').strip()
            result = eval(lhs, {'__builtins__': {}}, scope) == 0
        else:
            raise ValueError(f'Unsupported constraint row {idx}: {row}')
        if not result:
            failures.append({'row': idx, 'source': raw.strip()[:500]})
    return failures


def choose_zero_decoder(v, idx, x, target):
    delta = (x - target) % P
    v[idx] = inv(delta) if delta else F(0)
    v[idx + 1] = F(0 if delta else 1)


def make_witness(mod, current, a0=(1, 0, 0, 127)):
    v = [F(0) for _ in range(max(idx for idx, _ in mod.fields) + 1)]
    assert len(a0) == 4 and all(isinstance(i, int) and 0 <= i < 256 for i in a0)
    # syscall_recv: shard 1, clock 0, syscall read(4003), a1=0.
    v[0], v[2] = F(1), F(4003)
    for idx, value in enumerate(a0, start=3):
        v[idx] = F(value)
    packed = sum(byte * 256**i for i, byte in enumerate(a0)) % P
    compressed = (a0[0] + 256 * sum(a0[1:])) % P
    nonzero_read = (compressed if current else packed) != 0
    if nonzero_read:
        for idx in (11, 12, 13, 14):
            v[idx] = F(255)
        v[32] = F(9)
    for idx, target in [(41, 4210), (43, 4090), (45, 4120),
                        (47, 4246), (49, 4045), (51, 4055),
                        (53, 4003), (55, 4004)]:
        choose_zero_decoder(v, idx, 4003, target)
    if current:
        nop_syscalls = [4005, 4006, 4091, 4122, 4166, 4192,
                        4194, 4195, 4206, 4215, 4218, 4222,
                        4240, 4263, 4288, 4338, 4422]
        for idx, target in zip(range(58, 92, 2), nop_syscalls):
            choose_zero_decoder(v, idx, 4003, target)
        # No selected nop; all other syscall-class flags zero.
        v[92] = F(0)
        for idx, target in [(93, 0), (95, 1), (97, 2)]:
            choose_zero_decoder(v, idx, compressed, target)
        for idx, target in [(99, 1), (101, 3)]:
            choose_zero_decoder(v, idx, 0, target)
        # Derived public inputs: packed a0 wraps to 0 in KoalaBear in the
        # separating case. Separate 16-bit public argument limbs retain it.
        v[528] = F(packed)
        v[532], v[533] = F(a0[0] + 256*a0[1]), F(a0[2] + 256*a0[3])
        v[530], v[531] = F(65535 if nonzero_read else 0), F(65535 if nonzero_read else 0)
    else:
        for idx, target in [(58, 0), (60, 1), (62, 2)]:
            choose_zero_decoder(v, idx, packed, target)
        for idx, target in [(64, 1), (66, 3)]:
            choose_zero_decoder(v, idx, 0, target)
        v[458] = F(packed)
        v[462], v[463] = F(a0[0] + 256*a0[1]), F(a0[2] + 256*a0[3])
        v[460], v[461] = F(65535 if nonzero_read else 0), F(65535 if nonzero_read else 0)
    return v


def audit(old_path, new_path, lib_path):
    assert re.search(r'^abbrev KB : ℕ := 2130706433\b', lib_path.read_text(), re.M)
    old = next(m for m in scan_file(old_path)[1] if m.fields)
    new = next(m for m in scan_file(new_path)[1] if m.fields)
    assert len(old.constraint_lines) == 352 and len(new.constraint_lines) == 404
    old_w = make_witness(old, False)
    new_w = make_witness(new, True)
    old_failures, new_failures = check_constraints(old, old_w), check_constraints(new, new_w)
    old_ins = [int(old_w[i]) for i in old.ports['inputs']]
    new_ins = [int(new_w[i]) for i in new.ports['inputs']]
    old_outs = [int(old_w[i]) for i in old.ports['outputs']]
    new_outs = [int(new_w[i]) for i in new.ports['outputs']]
    # Positive control: ordinary zero argument agrees across both source forms.
    old_benign = make_witness(old, False, (0, 0, 0, 0))
    new_benign = make_witness(new, True, (0, 0, 0, 0))
    benign_old_failures = check_constraints(old, old_benign)
    benign_new_failures = check_constraints(new, new_benign)
    benign_agrees = (
        [int(old_benign[i]) for i in old.ports['inputs']]
        == [int(new_benign[i]) for i in new.ports['inputs']]
        and [int(old_benign[i]) for i in old.ports['outputs']]
        == [int(new_benign[i]) for i in new.ports['outputs']]
    )
    # Negative controls: attempt the opposite branch's public outputs while
    # leaving the source-derived read decoder for each version intact.
    old_wrong = old_w.copy()
    for idx in (11, 12, 13, 14):
        old_wrong[idx] = F(255)
    old_wrong[32] = F(9)
    old_wrong[460], old_wrong[461] = F(65535), F(65535)
    new_wrong = new_w.copy()
    for idx in (11, 12, 13, 14):
        new_wrong[idx] = F(0)
    new_wrong[32] = F(0)
    new_wrong[530], new_wrong[531] = F(0), F(0)
    cross_old_failures = check_constraints(old, old_wrong)
    cross_new_failures = check_constraints(new, new_wrong)
    return {
        'status': 'FULL_MODULE_SOURCE_EVALUATOR_REPLAY_NOT_LEAN_KERNEL_CHECK',
        'archive_sha256': hashlib.sha256(old_path.read_bytes()).hexdigest(),
        'current_sha256': hashlib.sha256(new_path.read_bytes()).hexdigest(),
        'field_definition_sha256': hashlib.sha256(lib_path.read_bytes()).hexdigest(),
        'old_constraints_checked': len(old.constraint_lines),
        'new_constraints_checked': len(new.constraint_lines),
        'old_constraint_failures': old_failures,
        'new_constraint_failures': new_failures,
        'benign_archive_constraint_failures': benign_old_failures,
        'benign_current_constraint_failures': benign_new_failures,
        'benign_same_inputs_and_outputs': benign_agrees,
        'negative_archived_with_current_outputs_failed_row_count': len(cross_old_failures),
        'negative_current_with_archived_outputs_failed_row_count': len(cross_new_failures),
        'negative_archived_failed_row_indices': [row['row'] for row in cross_old_failures],
        'negative_current_failed_row_indices': [row['row'] for row in cross_new_failures],
        'same_public_inputs': old_ins == new_ins,
        'different_public_outputs': old_outs != new_outs,
        'public_inputs': old_ins,
        'archived_public_outputs': old_outs,
        'current_public_outputs': new_outs,
        'archived_nonzero_assignments': {f'v{i}': int(x) for i, x in enumerate(old_w) if x},
        'current_nonzero_assignments': {f'v{i}': int(x) for i, x in enumerate(new_w) if x},
        'current_relation_uniqueness': 'UNKNOWN',
        'whole_vm_reachability': 'UNKNOWN',
    }


def emit_lean_fixture(source, mod, v, ins, outs, dest, archived):
    """Retain every original definition verbatim, drop unrelated proof search.

    The old source has ~16MB of generated theorem proof machinery after rel.
    No original witness field, constraint or port definition is rewritten.
    This emitted file is suitable for `lake env lean` in the matching crate.
    """
    src = source.read_text()
    marker = '\ndef cj0 ' if archived else '\ntheorem deterministic'
    assert src.count(marker) == 1, marker
    prefix = src.split(marker, 1)[0]
    assert 'def rel (ins outs : List F)' in prefix
    assert 'def outputs (w : W)' in prefix
    assignments = ',\n    '.join(f'v{i} := {int(v[i])}' for i, _ in mod.fields)
    list_expr = lambda xs: '[' + ', '.join(str(x) for x in xs) + ']'
    constraint_defs = ' '.join(f'constraints_{i}' for i in range(8 if archived else 9))
    appended = f'''

/-! MathGraph exact-source full SysLinux read witness replay.
    Source sha256: {hashlib.sha256(source.read_bytes()).hexdigest()}
    Definitions above are an unchanged byte-prefix of the native generated file.
    Nonessential generated determinism proof-search follows after this prefix
    in the archived source; it is not used in the witness proof. -/
def mathGraphReadWitness : W := {{
    {assignments}
  }}

theorem mathGraphReadWitness_constraints : constraints mathGraphReadWitness := by
  unfold constraints {constraint_defs}
  decide

theorem mathGraphReadWitness_inputs : inputs mathGraphReadWitness = {list_expr(ins)} := by
  decide

theorem mathGraphReadWitness_outputs : outputs mathGraphReadWitness = {list_expr(outs)} := by
  decide

theorem mathGraphReadWitness_rel : rel {list_expr(ins)} {list_expr(outs)} := by
  exact ⟨mathGraphReadWitness, mathGraphReadWitness_constraints,
    mathGraphReadWitness_inputs, mathGraphReadWitness_outputs⟩

#print axioms mathGraphReadWitness_rel
end SysLinux
end ZirenDet.Chips.SysLinux
#print "MATHGRAPH_SYSLINUX_REL_WITNESS_DONE"
'''
    dest.write_text(prefix + appended)


def main():
    parser = argparse.ArgumentParser()
    for opt in ('old', 'new', 'lib'):
        parser.add_argument(f'--{opt}', type=Path, required=True)
    parser.add_argument('--emit-lean-dir', type=Path)
    args = parser.parse_args()
    result = audit(args.old, args.new, args.lib)
    if args.emit_lean_dir:
        args.emit_lean_dir.mkdir(parents=True, exist_ok=True)
        old = next(m for m in scan_file(args.old)[1] if m.fields)
        new = next(m for m in scan_file(args.new)[1] if m.fields)
        old_w = make_witness(old, False)
        new_w = make_witness(new, True)
        emit_lean_fixture(args.old, old, old_w,
                          result['public_inputs'], result['archived_public_outputs'],
                          args.emit_lean_dir / 'MathGraphArchivedSysLinux.lean', True)
        emit_lean_fixture(args.new, new, new_w,
                          result['public_inputs'], result['current_public_outputs'],
                          args.emit_lean_dir / 'MathGraphCurrentSysLinux.lean', False)
    print(json.dumps(result, sort_keys=True, indent=2))
    if result['old_constraint_failures'] or result['new_constraint_failures']:
        sys.exit(1)
    if result['benign_archive_constraint_failures'] or result['benign_current_constraint_failures']:
        sys.exit(1)
    if not result['benign_same_inputs_and_outputs']:
        sys.exit(1)
    if not result['negative_archived_with_current_outputs_failed_row_count']:
        sys.exit(1)
    if not result['negative_current_with_archived_outputs_failed_row_count']:
        sys.exit(1)
    if not result['same_public_inputs'] or not result['different_public_outputs']:
        sys.exit(1)


if __name__ == '__main__':
    main()
