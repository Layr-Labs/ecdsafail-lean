"""Export ordered HMR seam ports and Builder allocations from the pinned source."""
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
borrows = []
fold_temporary = []
active_call = None
active_fold = None
call_start_ops = {}
call_operation_counts = {}
class Captured(Exception):
    pass

def allocated(b):
    return [q for q in range(b.next_qubit) if q not in b._free_set]

def snap(inv, y, out, ma, kind):
    w = inv.walk
    free = set(sum(w.pool.free.values(), []))
    return {'phase': inv.b.current_phase, 'kind': kind,
        'row': {'sign': w.fv.sign, 'payload': list(w.fv.ids)},
        'y': list(y), 'out': list(out),
        'ma': {k: list(v) if isinstance(v, list) else v for k,v in ma.items()
               if k in ['carry','flag','top','tq','clean3','anc']},
        'allocated': allocated(inv.b), 'home_free': sorted(free),
        'walk_live': sorted(set(allocated(inv.b))-free)}

original_on = E.MulMachine.on
original_mul = E.DivstepInvBase.row_mul
original_unpark = E.DivstepInvBase.row_unpark
original_fold = E.DivstepInvBase._fold_stage
original_qubit = Builder.qubit
original_recycle = Builder.recycle

def capture_on(mm, k, seam=False):
    before = allocated(mm.b)
    original_on(mm, k, seam=seam)
    if seam:
        after = allocated(mm.b)
        borrows.append({'phase': mm.b.current_phase, 'before_allocated': before,
                        'after_allocated': after,
                        'new': sorted(set(after)-set(before)),
                        'anc': list(mm.ma['anc']), 'flag': mm.ma['flag']})

def capture_mul(obj, y, out, ma, inv=False):
    global active_call
    records.append(snap(obj,y,out,ma,'erase' if inv else 'forward'))
    assert not obj.b._loop_stack
    active_call = len(records)-1
    call_start_ops[active_call] = len(obj.b._target())
    try:
        result = original_mul(obj,y,out,ma,inv=inv)
        call_operation_counts[active_call] = len(obj.b._target())-call_start_ops[active_call]
    finally:
        active_call = None
    if inv:
        raise Captured()
    return result

def capture_qubit(b, *args, **kwargs):
    wire = original_qubit(b, *args, **kwargs)
    if active_fold is not None:
        active_fold['allocations'].append(wire)
        active_fold['allocate_source_op'] = len(b._target())-call_start_ops[active_call]
    return wire

def capture_recycle(b, wire, *args, **kwargs):
    if active_fold is not None:
        active_fold['releases'].append(wire)
        active_fold['release_source_op'] = len(b._target())-call_start_ops[active_call]
    return original_recycle(b,wire,*args,**kwargs)

def capture_fold(obj, mode, reg, anc, alive=None):
    global active_fold
    if active_call is None or alive is not None:
        return original_fold(obj,mode,reg,anc,alive=alive)
    before = set(allocated(obj.b))
    assert before == set(records[active_call]['allocated'])
    event = {'call_index':active_call, 'mode':mode, 'allocations':[], 'releases':[]}
    active_fold = event
    try:
        result = original_fold(obj,mode,reg,anc,alive=alive)
    finally:
        active_fold = None
    assert len(event['allocations']) == 1, event
    wire = event.pop('allocations')[0]
    assert event.pop('releases') == [wire]
    assert wire not in before
    assert set(allocated(obj.b)) == before
    assert wire in obj.b._free_set
    event.update(wire=wire, before_count=len(before), after_count=len(before),
                 free_before=True, returned_free=True)
    fold_temporary.append(event)
    return result

def capture_unpark(inv, zeros, ma):
    previous = records[-1]
    records.append(snap(inv,zeros,previous['out'],ma,'unpark'))
    return original_unpark(inv,zeros,ma)

Builder.qubit = capture_qubit
Builder.recycle = capture_recycle
E.DivstepInvBase._fold_stage = capture_fold
E.MulMachine.on = capture_on
E.DivstepInvBase.row_mul = capture_mul
E.DivstepInvBase.row_unpark = capture_unpark
try:
    C.build_circuit(Builder())
except Captured:
    pass
assert [r['kind'] for r in records] == ['forward','unpark','forward','erase']
assert len(borrows)==2
for r in records:
    ma=r['ma']
    assert ma['carry'] is None and ma['top'] is None and ma['tq'] is None
    assert ma['clean3']==[] and len(ma['anc'])==24
    data=[r['row']['sign']]+r['row']['payload']+r['y']+r['out']
    ports=data+[ma['flag']]+ma['anc']
    assert len(r['row']['payload'])==280 and len(r['y'])==len(r['out'])==256
    assert len(set(ports))==len(ports), (r['phase'],r['kind'],'alias')
    assert set(ports)<=set(r['allocated'])
for b in borrows:
    assert set(b['new'])==set(b['anc'])|{b['flag']}
a.output.write_text(json.dumps({'source_commit':PIN,
    'engine_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'entry_sha256':hashlib.sha256(entry.read_bytes()).hexdigest(),
    'entry':str(entry.relative_to(root)), 'qcap':935, 'wide':False,
    'note':'Actual ordered allocation data; not a state-cleanliness or execution proof.',
    'seam_borrows':borrows,'calls':records,'fold_temporary':fold_temporary,
    'call_operation_counts':call_operation_counts,
    'position_unit':'zero-based source operations within row_mul, including R and SWAP'},indent=2)+'\n')
print('Exported four call boundaries, two seam acquisitions, and', len(fold_temporary), 'temporary fold leases.')
