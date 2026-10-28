#!/usr/bin/env python3
"""Empirical mathematical predicates, NOT a gate simulation or probability proof.
See docs/ASSUMPTIONS_B5.md. Uses only Python's standard library.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import subprocess

P = 2**256 - 2**32 - 977
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
PIN = '64b5a13aa249f1360846657392e6c66817b26d0f'
EXPECTED_CONSTANTS_SHA256 = '53151704af9d417ce421272c9c0e8c5a6ed174161139055a07bb3b6058b4c376'
WORD, LOW, C = 2**256, 2**58, 2**32 + 977
CELLS = ['counter', 'history', 'deadline', 'window', 'scaling', 'row', 'lift', 'horner', 'sign']


def add(a, b):
    if a is None: return b
    if b is None: return a
    x, y = a; u, v = b
    if x == u and (y + v) % P == 0: return None
    m = ((3*x*x) * pow(2*y, -1, P) if a == b else (v-y)*pow(u-x, -1, P)) % P
    w = (m*m-x-u) % P
    return w, (m*(x-w)-y) % P


def scalar_table():
    table = []; q = G
    for _ in range(64):
        row = [None]
        for _ in range(15): row.append(add(row[-1], q))
        table.append(row)
        for _ in range(4): q = add(q, q)
    return table


def multiply(k, table):
    out = None
    for row in table:
        out = add(out, row[k & 15]); k >>= 4
    assert k == 0
    return out


def halve(r): return (r + (P if r & 1 else 0)) // 2

def no_borrow(r): return not (r & 1) or r % LOW >= C-1

def scaling(seed, count):
    good = True
    for _ in range(count):
        good &= no_borrow(seed); seed = halve(seed)
    return good, seed


def step(s):
    z, f, g, fv, gv = s
    if z >= 0 and g & 1:
        return -z, g, (g-f)//2, 2*gv, gv-fv
    bit = g % 2
    return z+1, f, (g+bit*f)//2, 2*fv, gv+bit*fv


def fits(x, width): return -(1 << width) <= x < (1 << width)


def trajectory(d, windows, caps, width, depth):
    s = (0, P, d, 0, 1); frozen = False; history = 0; active_rider = 0
    counter = not fits(s[0], width-1); hist_bad = False; early = d == 0; win_bad = False
    for t in range(533):
        if t >= 498 and not frozen: active_rider += 1
        old = s
        if not frozen:
            s = step(s)
            if t >= 498 and s[2] == 0: frozen = True
        if t+1 <= 498 and s[2] == 0: early = True
        counter |= not fits(s[0], width-1)
        win_bad |= any(not fits(v, w) for v, w in zip(s[1:], windows[t]))
        # trajectoryStore post-slot selector; parityControl is pre-slot g%2.
        if not frozen and s[0] <= 0 and s[3] % (1 << depth) == 0:
            history = 2*history + old[2] % 2
            hist_bad |= history >= (1 << caps[t])
    return [counter, hist_bad, early or not frozen, win_bad], s, active_rider


def fused(coefficient, operand, negate):
    a = abs(coefficient)
    lift_good = a < 2**280 and (coefficient >= 0 or (a-1) % LOW + 1 < LOW)
    folded = a % WORD + (a // WORD)*C
    row_good = folded < WORD; scan = folded % WORD
    r = 0; horner_good = operand < WORD
    for k in range(256):
        if (scan >> k) & 1:
            if k == 0: r = operand
            else:
                total = r + operand; carry = total >= WORD
                nxt = (total % WORD + (C if carry else 0)) % WORD
                horner_good &= (not carry or total % WORD % LOW + C < LOW)
                horner_good &= (nxt >> 229 < operand >> 229) == (nxt < operand)
                horner_good &= (nxt < operand) == carry
                r = nxt
        horner_good &= no_borrow(r); r = halve(r)
    tail_good, r = scaling(r, 242); horner_good &= tail_good
    sign_good = r < WORD and (not negate or (r <= P and C-1 <= (WORD-1-r) % LOW))
    return [not row_good, not lift_good, not horner_good, not sign_good]


def classify(point, fixed, windows, caps, width, depth):
    x, y = point; cx, cy = fixed
    d1 = (x-cx) % P; operand = (y-cy) % P
    slope = operand * pow(d1, -1, P) % P
    newx = (slope*slope-x-cx) % P; d2 = (cx-newx) % P
    if d2 == 0:
        return [False]*9  # dialogExceptionPoint: no enabled fused/inverse calls
    flags = [False]*9
    for i, d in enumerate([d1, d2]):
        base, rows, rider = trajectory(d, windows, caps, width, depth)
        for j in range(4): flags[j] |= base[j]
        # Existing fifth cell: canonical closed-inverse ScalingCallSites seed.
        seed = (rows[1]*rows[3]) % P
        flags[4] |= not scaling(seed, 498+rider)[0]
        op = operand if i == 0 else scaling(d*slope % P, rider)[1]
        extra = fused(rows[3], op, (rows[1] < 0) != (rows[3] < 0))
        for j in range(4): flags[j+5] |= extra[j]
    # s6 erase replays the same mathematical call, no independent resampling.
    return flags


def summary(counts, size):
    return {k: {'count': v, 'samples': size, 'estimate': v/size,
                'zero_count_note': f'≤ {3/size:.8g} (approximate per-cell 95% rule of three; not theorem)'
                if v == 0 else None} for k, v in counts.items()}


def check_record(path):
    r = json.loads(path.read_text())
    assert r['status'] == 'empirical estimate, NOT theorem'
    assert r['source_commit'] == PIN and r['group_order'] == str(N)
    assert r['script_sha256'] == hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    assert r['constants_sha256'] == EXPECTED_CONSTANTS_SHA256
    size = r['accepted']; assert isinstance(size, int) and size > 0
    assert r['attempted'] == size + sum(r['excluded'].values())
    assert set(r['excluded']) == {'infinity', 'equal_C', 'negative_C'}
    assert all(isinstance(v, int) and v >= 0 for v in r['excluded'].values())
    assert 0 <= r['fourth_corner_disabled_in_sample'] <= size
    assert r['C'] == [hex(v) for v in multiply(r['fixed_scalar'], scalar_table())]
    assert set(r['models']) == {'hmr_candidate_w6_j5', 'current_lean_w7_j7'}
    for m in r['models'].values():
        ex, raw = m['exclusive'], m['raw_diagnostics_not_additive']
        assert set(ex) == set(raw) == set(CELLS)
        for group in (ex, raw):
            for cell in group.values():
                c = cell['count']; assert isinstance(c, int) and 0 <= c <= size
                assert cell == summary({'x': c}, size)['x']
        total = sum(v['count'] for v in ex.values())
        assert total <= size
        assert all(ex[k]['count'] <= raw[k]['count'] for k in CELLS)
        assert m['observed_union_rate'] == total/size
        assert m['descriptive_2sqrt_rate'] == 2*(total/size)**0.5
    print('B5 empirical metadata/count consistency passed (not a probability proof).')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source', type=Path)
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--samples', type=int, default=10000)
    ap.add_argument('--seed', type=int, default=20261023)
    ap.add_argument('--fixed-scalar', type=int, default=1)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.check:
        check_record(args.output); return
    if args.source is None: ap.error('--source is required for sampling')
    if args.samples <= 0 or not 0 < args.fixed_scalar < N: ap.error('invalid sample count or fixed scalar')
    sha = subprocess.check_output(['git', '-C', str(args.source), 'rev-parse', 'HEAD'], text=True).strip()
    if sha != PIN: ap.error(f'expected source {PIN}, got {sha}')
    path = args.source/'tasks/modinv-point-add/circuits/divsteps/constants.json'
    blob = path.read_bytes()
    assert hashlib.sha256(blob).hexdigest() == EXPECTED_CONSTANTS_SHA256
    constants = json.loads(blob)
    windows = list(zip(*(constants['windows_q'][k] for k in ['WF','WG','WFV','WGV'])))
    caps = []; cap = 0
    for t, reach in enumerate(constants['spans_q']['reach']):
        cap = max(cap, min(min(reach, t)+1, 60)); caps.append(cap)
    assert len(windows) == len(caps) == 533 and constants['z']['Wz'] == 6
    table = scalar_table(); fixed = multiply(args.fixed_scalar, table)
    fourth = multiply((-2*args.fixed_scalar) % N, table)
    rng = random.Random(args.seed); excluded = {'infinity': 0, 'equal_C': 0, 'negative_C': 0}
    models = {'hmr_candidate_w6_j5': (6, 5), 'current_lean_w7_j7': (7, 7)}
    raw = {m: dict.fromkeys(CELLS, 0) for m in models}
    exclusive = {m: dict.fromkeys(CELLS, 0) for m in models}
    attempted = accepted = fourth_corner = 0; digest = hashlib.sha256()
    while accepted < args.samples:
        k = rng.randrange(1, N); attempted += 1
        digest.update(k.to_bytes(32, 'big')); point = multiply(k, table)
        if point is None: excluded['infinity'] += 1; continue
        if point == fixed: excluded['equal_C'] += 1; continue
        if point == (fixed[0], (-fixed[1]) % P): excluded['negative_C'] += 1; continue
        if point == fourth: fourth_corner += 1
        for model, (width, depth) in models.items():
            flags = classify(point, fixed, windows, caps, width, depth)
            for cell, failed in zip(CELLS, flags): raw[model][cell] += int(failed)
            if any(flags): exclusive[model][CELLS[flags.index(True)]] += 1
        accepted += 1
    result = {'status': 'empirical estimate, NOT theorem', 'source_commit': sha,
              'constants_sha256': hashlib.sha256(blob).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'group_order': str(N), 'seed': args.seed, 'prng': 'Python random.Random MT19937; randrange rejection sampling',
              'fixed_scalar': args.fixed_scalar, 'C': [hex(v) for v in fixed],
              'law': 'k uniform in [1,n-1], P=kG, control=true, conditional on P not in {O,C,-C}',
              'fourth_corner_disabled_in_sample': fourth_corner, 'accepted': accepted, 'attempted': attempted, 'excluded': excluded,
              'sample_scalar_sha256': digest.hexdigest(), 'models': {}}
    for model in models:
        total = sum(exclusive[model].values()) / accepted
        result['models'][model] = {'exclusive': summary(exclusive[model], accepted),
             'raw_diagnostics_not_additive': summary(raw[model], accepted),
             'observed_union_rate': total, 'descriptive_2sqrt_rate': 2*total**0.5}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__': main()
