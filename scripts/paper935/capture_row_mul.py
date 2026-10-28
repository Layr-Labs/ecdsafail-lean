"""Capture complete pinned row_mul streams and verify every template occurrence."""
from collections import Counter
from pathlib import Path
import hashlib
import json
import struct
import subprocess
import sys

PIN = '64b5a13aa249f1360846657392e6c66817b26d0f'
COUNTS = [2185556, 2185556, 2203069]


def capture(source):
    if sys.version_info < (3, 10):
        raise RuntimeError("Source replay needs Python >= 3.10; set ECDSA_SOURCE_PYTHON")
    source = Path(source).resolve()
    assert subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip() == PIN
    subprocess.run(['git', '-C', str(source), 'diff', '--exit-code', 'HEAD', '--'], check=True, stdout=subprocess.DEVNULL)
    sys.path.insert(0, str(source))
    from uncompute import Builder
    from uncompute.testing import load_module
    from uncompute.ops import OpKind, NO_QUBIT, NO_OUT, NO_REG, NO_BIT
    entry = source / 'tasks/modinv-point-add/circuits/divsteps/circuit.py'
    C = load_module(entry, 'row_mul_source_capture')
    E = C.E
    assert C.QCAP == 935
    templates = {}
    calls = []
    active = None
    block = None
    outcomes = {}
    measurements = 0
    old_emit, old_qubit, old_recycle = Builder._emit, Builder.qubit, Builder.recycle
    old_mul = E.DivstepInvBase.row_mul
    methods = {name: getattr(E.DivstepInvBase, name) for name in ('_row_lift', '_row_reduce', '_halve_out')}
    old_cma = E._mul_cma

    class Finished(Exception):
        pass

    def start_block(name, control=None):
        nonlocal block
        assert block is None
        block = {'name': name, 'control': control, 'raw_start': active['raw_count'],
                 'measurement_start': measurements, 'ops': [], 'borrows': []}

    def finish_block():
        nonlocal block
        assert block is not None
        name = block['name']
        if name in templates:
            assert templates[name] == block['ops'], (name, 'source template occurrence differs')
        else:
            templates[name] = block['ops']
        active['uses'].append({'template': name, 'control': block['control'],
                              'raw_start': block['raw_start'],
                              'measurement_start': block['measurement_start'] - active['measurement_start'],
                              'borrows': block['borrows']})
        block = None

    def finish_inline():
        if block is not None:
            assert block['name'] == 'copy'
            finish_block()

    def emit(self, kind, qa=NO_QUBIT, qb=NO_QUBIT, qt=NO_QUBIT, ot=NO_OUT,
             oc=NO_OUT, rt=NO_REG, ct=NO_BIT, cc=NO_BIT):
        nonlocal measurements
        if kind == OpKind.HMR:
            outcomes[ot] = measurements
            measurements += 1
        if active is not None:
            if block is None:
                start_block('copy')
            assert rt == NO_REG and ct == cc == NO_BIT
            name = OpKind(kind).name
            active['kinds'][name] += 1
            active['digest'].update(struct.pack('<9Q', *(int(x) & ((1 << 64) - 1) for x in (kind, qa, qb, qt, ot, oc, rt, ct, cc))))
            def wire(q):
                if block['control'] is not None and q == block['control']:
                    return 819
                assert q in active['wire_map'], (name, q, 'unmapped quantum operand')
                return active['wire_map'][q]
            if name in ('X', 'R'):
                assert oc == NO_OUT
                op = [name, wire(qt)]
            elif name in ('CX', 'SWAP'):
                assert oc == NO_OUT
                op = [name, wire(qb), wire(qt)]
            elif name == 'CCX':
                assert oc == NO_OUT
                op = [name, wire(qa), wire(qb), wire(qt)]
            elif name == 'HMR':
                assert oc == NO_OUT
                op = [name, wire(qt)]
            elif name in ('Z', 'CZ'):
                assert oc != NO_OUT and outcomes[oc] >= block['measurement_start'], (name, 'nonlocal outcome')
                ordinal = outcomes[oc] - block['measurement_start']
                op = [name, ordinal, wire(qt)] if name == 'Z' else [name, ordinal, wire(qb), wire(qt)]
            else:
                raise AssertionError(('unsupported source operation', name))
            block['ops'].append(op)
            active['raw_count'] += 1
        return old_emit(self, kind, qa=qa, qb=qb, qt=qt, ot=ot, oc=oc, rt=rt, ct=ct, cc=cc)

    def qubit(self):
        q = old_qubit(self)
        if active is not None:
            assert block is not None and block['name'].startswith('halve_')
            if q not in active['wire_map']:
                assert len(active['ports']) == 818
                active['ports'].append(q)
                active['wire_map'][q] = 818
            assert active['wire_map'][q] == 818
            block['borrows'].append([len(block['ops']), 818])
        return q

    def recycle(self, q, reset_recorded=False):
        if active is not None:
            assert not reset_recorded and active['wire_map'][q] == 818
            assert block['name'].startswith('halve_')
        return old_recycle(self, q, reset_recorded=reset_recorded)

    def lift(self, row, ma, inv_):
        if active is None:
            return methods['_row_lift'](self, row, ma, inv_)
        finish_inline(); start_block('lift_inverse' if inv_ else 'lift_forward')
        result = methods['_row_lift'](self, row, ma, inv_)
        finish_block(); return result

    def fold(self, row, zeros, ma, inv=False):
        if active is None:
            return methods['_row_reduce'](self, row, zeros, ma, inv=inv)
        finish_inline(); start_block('fold_inverse' if inv else 'fold_forward')
        result = methods['_row_reduce'](self, row, zeros, ma, inv=inv)
        finish_block(); return result

    def halve(self, out, anc, inv=False):
        if active is None:
            return methods['_halve_out'](self, out, anc, inv=inv)
        finish_inline(); start_block('halve_inverse' if inv else 'halve_forward')
        result = methods['_halve_out'](self, out, anc, inv=inv)
        finish_block(); return result

    def cma(b, ctrl, addend, target, p, n, ma, inv=False):
        if active is None:
            return old_cma(b, ctrl, addend, target, p, n, ma, inv=inv)
        finish_inline(); start_block('cma_inverse' if inv else 'cma_forward', ctrl)
        result = old_cma(b, ctrl, addend, target, p, n, ma, inv=inv)
        finish_block(); return result

    def row_mul(self, y, out, ma, inv=False):
        nonlocal active
        ports = [self.walk.fv.sign, *self.walk.fv.ids, *y, *out, *ma['anc'], ma['flag']]
        assert len(ports) == len(set(ports)) == 818
        active = {'name': 's6Erase' if inv else ('s2Forward' if not calls else 's6Forward'),
                  'phase': self.b.current_phase, 'ports': ports,
                  'wire_map': {q: i for i, q in enumerate(ports)}, 'uses': [],
                  'measurement_start': measurements, 'raw_count': 0, 'kinds': Counter(),
                  'digest': hashlib.sha256()}
        old_mul(self, y, out, ma, inv=inv)
        finish_inline()
        active['measurement_count'] = measurements - active['measurement_start']
        active['source_sha256'] = active.pop('digest').hexdigest()
        active.pop('wire_map')
        assert active['raw_count'] == COUNTS[len(calls)]
        assert active['measurement_count'] == 197474 and active['kinds']['R'] == 498
        assert len(active['ports']) == 819 and active['ports'][818] == (804 if not calls else 856)
        calls.append(active)
        active = None
        if inv:
            raise Finished()

    Builder._emit, Builder.qubit, Builder.recycle = emit, qubit, recycle
    E.DivstepInvBase.row_mul = row_mul
    E.DivstepInvBase._row_lift, E.DivstepInvBase._row_reduce, E.DivstepInvBase._halve_out = lift, fold, halve
    E._mul_cma = cma
    try:
        try:
            C.build_circuit(Builder())
        except Finished:
            pass
    finally:
        Builder._emit, Builder.qubit, Builder.recycle = old_emit, old_qubit, old_recycle
        E.DivstepInvBase.row_mul = old_mul
        for name, method in methods.items():
            setattr(E.DivstepInvBase, name, method)
        E._mul_cma = old_cma
    assert len(calls) == 3
    files = ['tasks/modinv-point-add/circuits/divsteps/engine.py',
             'tasks/modinv-point-add/circuits/divsteps/circuit.py',
             'tasks/modinv-point-add/circuits/_shared/luo_core.py', 'uncompute/builder.py']
    return {'source_commit': PIN, 'source_files': {f: hashlib.sha256((source/f).read_bytes()).hexdigest() for f in files},
            'templates': templates, 'calls': calls}

if __name__ == '__main__':
    result = capture(sys.argv[1])
    Path(sys.argv[2]).write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print('Captured all three complete source streams;', len(result['templates']), 'templates;',
          sum(len(x) for x in result['templates'].values()), 'template operations.')
