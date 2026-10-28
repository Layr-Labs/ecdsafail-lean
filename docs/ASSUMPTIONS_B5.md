# B5 assumptions and empirical measurements

## (i) Empirical estimates, NOT theorems

**Every number below is a sample estimate, not a proved population bound.**
The conditional Lean application assumes the nine population inequalities in
`EmpiricalBudget.bounds : FusedMassBounds μ events scaling (fusedFailures calls)`.
It does **not** construct them from sample counts. The nine observation indices
0–8 follow counter, history, deadline, window, scaling, row, lift, Horner, sign;
the nine named bound fields follow exactly that order. The sum of exclusive
counts is at most the accepted sample count. No independence is assumed.
Chosen bounds may differ from observed fractions; this report does not supply
proof terms for any numerical bounds or for a complete point-add circuit.

Dependent conditional theorems (namespace `ECDSAAdd.Arithmetic.Paper935`):
`empirical_nine_mass` gives the exact partition and the assumed total bound;
`empirical_calls_good` gives enabled modeled calls' numerical predicates on
good labels; `empirical_error` gives `2 * sqrt(b.bounds.total)` with additional
`RecordedAgreement`, `total < 1`, normalization and amplitude-law matching.
`hmrSource_empirical_error` gives the same symbolic `2 * sqrt(b.bounds.total)`
bound for the source-shaped three-call program, additionally requiring the
producer/caller execution conditions, complete output basis equality, total
phase-debt cancellation and equality with the typed circuit program. It depends
on both assumptions in this file; it supplies no numerical population bound
and does not certify the sampler or a complete point-addition instance.
The structure and these four theorems require a supplied `EmpiricalBudget`.
`EmpiricalBudget.observedRate` is descriptive only. Existing `fused_nine_mass`,
`fusedExactBounds_total`, `fused_error_exact` and `hmr_pre_of_not_bad` remain
unchanged: they do not depend on empirical observations. The physical consumer
`hmr_pre_of_not_bad` is in draft PR211 and still requires actual register binding;
it is not copied into this PR. No numerical literal ε is embedded in Lean.

Sampling uses `scripts/sample_b5.py` and the pinned source commit
`64b5a13aa249f1360846657392e6c66817b26d0f`, specifically
`tasks/modinv-point-add/circuits/divsteps/constants.json` for windows/spans.
The Python evaluator implements the mathematical `pinWalk`, `trajectoryEvents`,
`pointScalingFailure` and `fusedPointCalls` predicates; it is **not** a gate
simulator or a proved Python-to-Lean translation. Fifth-cell scaling is the
existing closed-inverse seed `(f * fv) mod p`, checked for the 498 seam halves
and armed rider, as in `ScalingCallSites`; it is not silently replaced by a
fused-output seed. Row/lift/Horner/sign use the two distinct fused call inputs;
the erase replay repeats the second call on the same label.

Both tables use S=533, Tmin=498, cap=60, the same source window schedule and
point samples. The 7-bit/threshold-7 table follows current main's
`authorTrajectoryEvents`. The 6-bit/threshold-5 table substitutes the selected
HMR counter/history parameters; it is a candidate mathematical event ledger,
**not** a certificate of the unfinished HMR compiler. No table establishes
source program agreement or the whole-machine 935 bound.

Each table references this ASSUMPTIONS_B5.md assumption. Zero-count entries
show **≤3/N (approximate per-cell 95% rule of three)**, a statistical diagnostic
under the specified sampling model, not a theorem or a simultaneous nine-cell
confidence bound. The point estimate is zero when no failure is observed;
that is not a claim that population failure probability is zero. N=10,000 is
an illustrative sample, too small to resolve much smaller rare-event rates.

**hmr_candidate_w6_j5 — empirical estimate, NOT theorem; [assumptions](#i-empirical-estimates-not-theorems).**

| Exclusive cell | Failures / N | Observed fraction | Zero-count diagnostic | Assumptions |
|---|---:|---:|---|---|
| counter | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| history | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| deadline | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| window | 1 / 10000 | 0.0001 | — | [B5](#i-empirical-estimates-not-theorems) |
| scaling | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| row | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| lift | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| horner | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| sign | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |

Observed union fraction: **0.0001**. Descriptive `2√(observed fraction)`: **0.02**, not a certified quantum error bound.

Raw diagnostic masses below are not exclusive and must not be added to the nine-cell total. They display the fifth and four route-A events separately.

| Raw event | Failures / N | Observed fraction | Zero-count diagnostic | Assumptions |
|---|---:|---:|---|---|
| scaling | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| row | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| lift | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| horner | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| sign | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
**current_lean_w7_j7 — empirical estimate, NOT theorem; [assumptions](#i-empirical-estimates-not-theorems).**

| Exclusive cell | Failures / N | Observed fraction | Zero-count diagnostic | Assumptions |
|---|---:|---:|---|---|
| counter | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| history | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| deadline | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| window | 1 / 10000 | 0.0001 | — | [B5](#i-empirical-estimates-not-theorems) |
| scaling | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| row | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| lift | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| horner | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| sign | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |

Observed union fraction: **0.0001**. Descriptive `2√(observed fraction)`: **0.02**, not a certified quantum error bound.

Raw diagnostic masses below are not exclusive and must not be added to the nine-cell total. They display the fifth and four route-A events separately.

| Raw event | Failures / N | Observed fraction | Zero-count diagnostic | Assumptions |
|---|---:|---:|---|---|
| scaling | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| row | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| lift | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| horner | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |
| sign | 0 / 10000 | 0 | ≤0.0003 (approx. 95%, per cell) | [B5](#i-empirical-estimates-not-theorems) |

## (ii) Original-point-induced input law, NOT a uniform denominator law

**μ is the law specified here, not a universal law for all point additions.**
Original labels are control=true and P=kG, with k sampled uniformly in
[1,n−1], conditioned on P not in {O,C,−C}. The control=false branch has no
inverse invocation and is outside this sampling law. C is an explicit script
parameter, here `--fixed-scalar 1`, so C=G. The two denominators are computed
jointly from the same P: d₁=X−cx and d₂=cx−(λ²−X−cx), with
λ=(Y−cy)/(X−cx). Their joint law is the deterministic pushforward of μ,
not two fresh uniform field draws. The Lean theorem `induced_denominator_mass`
expresses this pushforward for any supplied μ and map. The conditional three
`empirical_*` theorems above are applied to this μ only if its event bounds and
all their other premises are supplied. None automatically certifies this Python
sampler's law.

The fourth corner P=−2C (`dialogExceptionPoint C`) is **kept** in the accepted
sample population, counted separately, and has disabled calls; it contributes
to no nine-cell failure. It is not an extra conditional exclusion. This follows
the existing call model, not a newly sampled zero-inverse convention.

Actual parameters: group order n=`115792089237316195423570985008687907852837564279074904382605163141518161494337`; C.x=`0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798`; C.y=`0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8`; seed=`20261023`; accepted N=`10000`; attempted=`10000`. Python `random.Random` MT19937 with `randrange` rejection sampling, with replacement. The seed fixes a reproducible pseudorandom experiment, not a proof of random population bounds.

| Category | Count | Treatment |
|---|---:|---|
| infinity | 0 | Excluded before accepted N; no ε contribution |
| equal_C | 0 | Excluded before accepted N; no ε contribution |
| negative_C | 0 | Excluded before accepted N; no ε contribution |
| Fourth exceptional corner | 0 | Calls disabled; kept in N; no nine-cell contribution |
| Exclusive failure (each model) | 1 | Kept in N |
| Ordinary success (each model) | 9999 | Kept in N |

Three excluded counts + fourth corner + exclusive failures + ordinary successes = attempted draws. Fourth corner + exclusive failures + ordinary successes = accepted N.

Script SHA256: `f0f0aadef87f240d310e894385c72c7ec208dc72721349a6898483f60328780a`. Constants SHA256: `53151704af9d417ce421272c9c0e8c5a6ed174161139055a07bb3b6058b4c376`. Scalar sequence SHA256: `c3ea7660bf1dd6675b8e39cd098b3874faf1241b5788186b651bba9a712636c5`. Full metadata, raw counts and exclusive counts are in [data/b5-empirical.json](../data/b5-empirical.json).

Reproduce with the pinned source checkout:

```sh
python3 scripts/sample_b5.py --source /path/to/uncompute --samples 10000 --seed 20261023 --fixed-scalar 1 --output /tmp/b5-empirical.json
cmp data/b5-empirical.json /tmp/b5-empirical.json
python3 scripts/sample_b5.py --check --output data/b5-empirical.json
```

`verify.sh` runs the metadata/count consistency checker and boundary tests.
The checker verifies the script/constants pins, point parameter and count/rate
arithmetic, not population bounds or gate execution. The reproducibility check
reruns the experiment and compares bytes. No empirical-to-bound proof instance
is shipped. The physical good-input and quantum bridge obligations remain open.
