"""Check the Lean snapshot constants against the pinned source journal export.

This checks data transcription, not the compiled-walk/source correspondence.
The Lean kernel checks the ownership and readiness theorems separately.
"""
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[2]
data = json.loads((root / 'data/fused-hmr935-repack.json').read_text())
lean = (root / 'ECDSAAdd/Arithmetic/Paper935/FusedSourceRepack.lean').read_text()
assert data['source_commit'] == '64b5a13aa249f1360846657392e6c66817b26d0f'
assert data['entry'] == 'tasks/modinv-point-add/circuits/divsteps/circuit.py'
assert data['qcap'] == 935 and data['wide'] is False
assert len(data['closers']) == 2
for name, record in zip(('s2', 's6'), data['closers']):
    section = lean.split(f'def {name}SourceLive : Finset Wire :=', 1)[1].split('\ntheorem', 1)[0]
    intervals = [(int(a), int(b)) for a, b in re.findall(r'\((\d+) ≤ q ∧ q < (\d+)\)', section)]
    actual = {q for a, b in intervals for q in range(a, b)}
    before = record['before']
    expected = set(before['allocated']) - set(sum(before['free'].values(), []))
    assert actual == expected, (name, 'live snapshot mismatch')
    section = lean.split(f'def {name}SourceRepack : List (Wire × Wire) :=', 1)[1].split('\ntheorem', 1)[0]
    moves = [(int(a), int(b)) for a, b in re.findall(r'\((\d+), (\d+)\)', section)]
    assert moves == [(m['old'], m['fresh']) for m in record['moves']], name
    for old, fresh in moves:
        assert old in actual and fresh not in actual
        actual.remove(old)
        actual.add(fresh)
    after = record['after']
    assert actual == set(after['allocated']) - set(sum(after['free'].values(), [])), name
print('Both Lean source snapshots and journals match the pinned export.')
