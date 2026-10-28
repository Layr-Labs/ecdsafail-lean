"""Check source JSON against Lean seam constants, not circuit semantics."""
import ast
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[2]
data = json.loads((root / 'data/hmr-call-ports.json').read_text())
lean = (root / 'ECDSAAdd/Arithmetic/Paper935/HmrSourceCallPorts.lean').read_text()
assert data['source_commit'] == '64b5a13aa249f1360846657392e6c66817b26d0f'
assert data['entry'] == 'tasks/modinv-point-add/circuits/divsteps/circuit.py'
assert data['qcap'] == 935 and data['wide'] is False
assert [r['kind'] for r in data['calls']] == ['forward', 'unpark', 'forward', 'erase']
assert len(data['seam_borrows']) == 2
assert len(data['fold_temporary']) == 1494
assert data['call_operation_counts'] == {'0':2185556,'2':2185556,'3':2203069}
assert data['position_unit'] == 'zero-based source operations within row_mul, including R and SWAP'
for absent in ('carry', 'top', 'tq'):
    assert re.search(r'def HmrSeamPorts\.' + absent +
        r' \(_ : HmrSeamPorts\) : Option Wire := none', lean)
assert 'def HmrSeamPorts.clean3 (_ : HmrSeamPorts) : List Wire := []' in lean

def extract(pattern):
    match = re.search(pattern, lean)
    assert match, pattern
    return match.groups()

for tag, pair, borrow in zip(('s2', 's6'),
        (data['calls'][:2], data['calls'][2:]), data['seam_borrows']):
    record, later = pair
    layout, = extract(r'def ' + tag + r'HmrSourceLayout : HmrRowMulLayout where([\s\S]*?)  row_length :=')
    fields = {'row': tag + 'HmrSourceRow', 'y': tag + 'HmrSourceY',
              'out': tag + 'HmrSourceOut', 'anc': tag + 'HmrSeamPorts.anc',
              'flags': '{' + tag + 'HmrSeamPorts.flag, ' + tag + 'HmrFoldTemporary}'}
    actual = dict(re.findall(r'^  (\w+) := ([^\n]+)$', layout, re.M))
    assert actual == fields, (tag, 'layout reference mismatch', actual)
    for key in ('row', 'y', 'out', 'ma'):
        assert record[key] == later[key], (tag, key, 'boundary changed')
    flag, anc = extract(r'def ' + tag + r'HmrSeamPorts : HmrSeamPorts := ⟨(\d+), (\[[^\n]*\]),')
    anc = ast.literal_eval(anc)
    assert int(flag) == record['ma']['flag'] == borrow['flag']
    assert anc == record['ma']['anc'] == borrow['anc']
    assert record['ma']['carry'] is None and record['ma']['top'] is None
    assert record['ma']['tq'] is None and record['ma']['clean3'] == []
    start, count, tail, sign = extract(r'def ' + tag +
        r"HmrSourceRow : WindowRow := ⟨\(List.range' (\d+) (\d+)\).reverse \+\+ (\[[^\n]*\]), (\d+)⟩")
    row = list(reversed(range(int(start), int(start) + int(count)))) + ast.literal_eval(tail)
    assert row == record['row']['payload'] and int(sign) == record['row']['sign']
    for field, key in (('Y', 'y'), ('Out', 'out')):
        start, count = extract(r'def ' + tag + r'HmrSource' + field +
                               r" : List Wire := List.range' (\d+) (\d+)")
        assert list(range(int(start), int(start) + int(count))) == record[key]
    for suffix, key in (('BeforeSeam', 'before_allocated'),
                        ('ExportedAfterSeam', 'after_allocated')):
        missing, = extract(r'def ' + tag + r'Hmr' + suffix +
                           r' : Arena :=\s*⟨arenaWires \\ \{([\d, ]+)\},')
        actual = set(range(935)) - {int(q) for q in missing.split(',')}
        assert actual == set(borrow[key]), (tag, key)
    assert set(borrow['new']) == {int(flag), *anc}
    assert set(borrow['before_allocated']).isdisjoint(borrow['new'])
    assert set(borrow['after_allocated']) == set(borrow['before_allocated']) | set(borrow['new'])
    temporary, = extract(r'def ' + tag + r'HmrFoldTemporary : Wire := (\d+)')
    temporary = int(temporary)
    missing, = extract(r'def ' + tag + r'HmrCallArena : Arena :=\s*⟨arenaWires \\ \{([\d, ]+)\},')
    actual = set(range(935)) - {int(q) for q in missing.split(',')}
    assert actual == set(record['allocated']), (tag, 'call arena')
    assert temporary not in actual
    for index in ((0,) if tag == 's2' else (2, 3)):
        events = [e for e in data['fold_temporary'] if e['call_index'] == index]
        assert len(events) == 498
        previous = -1
        for event in events:
            assert event['wire'] == temporary
            assert event['mode'] == ('double' if index == 3 else 'halve')
            assert event['before_count'] == event['after_count'] == len(record['allocated'])
            assert event['free_before'] is True and event['returned_free'] is True
            allocate, release = event['allocate_source_op'], event['release_source_op']
            assert previous < allocate < release < data['call_operation_counts'][str(index)]
            previous = release
    for boundary in pair:
        assert set(boundary['walk_live']) == set(boundary['allocated']) - set(boundary['home_free'])
print('Both ordered HMR seam layouts and independent allocation snapshots match the pinned export.')
