"""Replay the pinned source and capture the two gaps between actual row calls."""
from pathlib import Path
import hashlib
import subprocess
import sys

from capture_row_mul import PIN


def capture(source):
    source = Path(source).resolve()
    assert subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip() == PIN
    subprocess.run(['git', '-C', str(source), 'diff', '--exit-code', 'HEAD', '--'], check=True, stdout=subprocess.DEVNULL)
    sys.path.insert(0, str(source))
    from uncompute import Builder
    from uncompute.testing import load_module
    from uncompute.ops import OpKind, NO_QUBIT, NO_OUT, NO_REG, NO_BIT
    entry = source / 'tasks/modinv-point-add/circuits/divsteps/circuit.py'
    C = load_module(entry, 'lifecycle_source_capture')
    E = C.E
    assert C.QCAP == 935
    old_emit = Builder._emit
    old_mul, old_unpark, old_sign = E.DivstepInvBase.row_mul, E.DivstepInvBase.row_unpark, E.DivstepInvBase.sign_fix
    measurements, outcomes, calls, active = 0, {}, [], None

    class Finished(Exception):
        pass

    def emit(self, kind, qa=NO_QUBIT, qb=NO_QUBIT, qt=NO_QUBIT, ot=NO_OUT,
             oc=NO_OUT, rt=NO_REG, ct=NO_BIT, cc=NO_BIT):
        nonlocal measurements
        if kind == OpKind.HMR:
            outcomes[ot] = measurements
            measurements += 1
        if active is not None:
            assert rt == NO_REG and ct == cc == NO_BIT
            tag = OpKind(kind).name
            if tag in ('X', 'HMR'):
                assert oc == NO_OUT
                op = [tag, qt]
            elif tag in ('CX', 'SWAP'):
                assert oc == NO_OUT
                op = [tag, qb, qt]
            elif tag == 'CCX':
                assert oc == NO_OUT
                op = [tag, qa, qb, qt]
            elif tag in ('Z', 'CZ'):
                assert oc != NO_OUT and oc in outcomes
                op = [tag, outcomes[oc], qt] if tag == 'Z' else [tag, outcomes[oc], qb, qt]
            else:
                raise AssertionError(('unsupported gap operation', tag))
            active['ops'].append(op)
        return old_emit(self, kind, qa=qa, qb=qb, qt=qt, ot=ot, oc=oc, rt=rt, ct=ct, cc=cc)

    def finish():
        nonlocal active
        active['measurementEnd'] = measurements
        calls.append(active)
        active = None

    def mul(self, y, out, ma, inv=False):
        nonlocal active
        if inv:
            assert active is not None and active['name'] == 's6'
            finish()
            raise Finished()
        old_mul(self, y, out, ma, inv=inv)
        assert active is None
        active = {'name': 's2' if not calls else 's6', 'measurementStart': measurements,
                  'y': list(y), 'out': list(out), 'row': list(self.walk.fv.ids),
                  'rowSign': self.walk.fv.sign, 'fSign': self.walk.f.sign,
                  'anc': list(ma['anc']), 'ops': [], 'signParts': []}

    def unpark(self, borrow, ma):
        assert active is not None and active['name'] == 's2'
        finish()
        return old_unpark(self, borrow, ma)

    def sign(self, target, ma, inv=False):
        assert active is not None
        begin = len(active['ops'])
        old_sign(self, target, ma, inv=inv)
        active['signParts'].append({'inverse': inv, 'begin': begin, 'end': len(active['ops'])})

    Builder._emit = emit
    E.DivstepInvBase.row_mul, E.DivstepInvBase.row_unpark, E.DivstepInvBase.sign_fix = mul, unpark, sign
    try:
        try:
            C.build_circuit(Builder(), C.P_MOD, C.N)
        except Finished:
            pass
        assert len(calls) == 2
    finally:
        Builder._emit = old_emit
        E.DivstepInvBase.row_mul, E.DivstepInvBase.row_unpark, E.DivstepInvBase.sign_fix = old_mul, old_unpark, old_sign
    return {'sourceCommit': PIN, 'entry': str(entry.relative_to(source)),
            'entrySha256': hashlib.sha256(entry.read_bytes()).hexdigest(),
            'engineSha256': hashlib.sha256((entry.parent / 'engine.py').read_bytes()).hexdigest(), 'calls': calls}
