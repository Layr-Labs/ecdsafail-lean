"""Export public source closer journals; no numerical correctness claim."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

PIN = '64b5a13aa249f1360846657392e6c66817b26d0f'
p = argparse.ArgumentParser()
p.add_argument('--source', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
root = a.source.resolve()
head = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
if head != PIN:
    raise SystemExit('Source commit does not match the approved pin')
subprocess.run(['git', '-C', str(root), 'diff', '--exit-code', 'HEAD', '--'],
               check=True, stdout=subprocess.DEVNULL)
sys.path.insert(0, str(root))
from uncompute import Builder
from uncompute.testing import load_module
source = root / 'tasks/modinv-point-add/circuits/divsteps/engine.py'
entry = source.with_name('circuit.py')
C = load_module(entry, 'fused_journal_circuit')
E = C.E
assert C.QCAP == 935

records = []
inside_closer = False
class Captured(Exception):
    pass

def snapshot(w):
    b = w.b
    return {
        'phase': b.current_phase,
        'rows': {name: {'payload': list(getattr(w, name).ids), 'sign': getattr(w, name).sign}
                 for name in ['fv', 'g', 'gv', 'f']},
        'free': {name: list(ids) for name, ids in w.pool.free.items()},
        'owner': dict(sorted(w.pool.owner.items())),
        'allocated': [q for q in range(b.next_qubit) if q not in b._free_set],
    }

original_repack = E.WalkWBase._repack
original_closer = E.WalkWBase.closer

def record_repack(w):
    if not inside_closer:
        return original_repack(w)
    before = snapshot(w)
    start = len(w._tape)
    original_repack(w)
    after = snapshot(w)
    moves = []
    for kind, row, i, home in w._tape[start:]:
        assert kind == 'm'
        name = next(name for name in ['fv', 'g', 'gv', 'f'] if getattr(w, name) is row)
        moves.append({'row': name, 'index': i, 'home': home,
                      'old': before['rows'][name]['payload'][i], 'fresh': row.ids[i]})
    # Home-band free slots remain builder-allocated. Logical ownership excludes
    # them; check each public transaction, without asserting readiness.
    live = set(before['allocated']) - set(sum(before['free'].values(), []))
    for move in moves:
        assert move['old'] in live and move['fresh'] not in live
        assert 0 <= move['old'] < 935 and 0 <= move['fresh'] < 935
        live.remove(move['old'])
        live.add(move['fresh'])
    assert live == set(after['allocated']) - set(sum(after['free'].values(), []))
    records.append({'before': before, 'moves': moves, 'after': after})

def record_closer(w):
    global inside_closer
    inside_closer = True
    try:
        original_closer(w)
    finally:
        inside_closer = False
    if len(records) == 2:
        raise Captured()

E.WalkWBase._repack = record_repack
E.WalkWBase.closer = record_closer
b = Builder()
try:
    C.build_circuit(b)
except Captured:
    pass
assert len(records) == 2, 'Expected s2 and s6 closer snapshots'
a.output.write_text(json.dumps({'source_commit': PIN,
    'engine_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'entry': str(entry.relative_to(root)), 'qcap': C.QCAP, 'wide': False,
    'entry_sha256': hashlib.sha256(entry.read_bytes()).hexdigest(),
    'note': 'Public allocation data only; not a correctness or peak theorem.',
    'closers': records}, indent=2) + '\n')
print(json.dumps({'entry': str(entry.relative_to(root)), 'qcap': C.QCAP, 'wide': False,
    'entry_sha256': hashlib.sha256(entry.read_bytes()).hexdigest(),
    'moves': [len(r['moves']) for r in records],
    'allocated_before': [len(r['before']['allocated']) for r in records],
    'allocated_after': [len(r['after']['allocated']) for r in records]}))
