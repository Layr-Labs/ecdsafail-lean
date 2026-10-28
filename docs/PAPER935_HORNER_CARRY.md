# Author Horner copy and quantum carry sweeps

Source: `uncompute-paper` commit `64b5a13aa249f1360846657392e6c66817b26d0f`.
Paths below are relative to `tasks/modinv-point-add/circuits/`.

These are the copy and carry-sweep blocks of the fused endpoint implementation. They do
not yet implement the lazy modular adder or establish its successful-input
conditions. In particular, a cleanup identity is not forward arithmetic
correctness for a controlled modular addition.

| Lean definition | Author source | Meaning |
| --- | --- | --- |
| `hornerCopy` | `divsteps/engine.py:3026–3028`, inverse `3033–3036` | Increasing-order CCX fan for the first forward / last inverse Horner round |
| `hornerCarryForward` | `_shared/luo_core.py:882–894` | Quantum/quantum carry cell; both operands are dressed by the incoming carry |
| `hornerCarryBackward` | `_shared/luo_core.py:897–910` | Optional measured AND release with correction, optional controlled sum, then operand undressing |
| `hornerCarrySweep` | `_shared/luo_core.py:882–894` | Increasing forward sweep |
| `hornerCarryUnsweep` | `_shared/luo_core.py:897–910` | Descending cleanup, retaining only the highest carry when requested |
| `hornerCarryTop` | `_shared/luo_core.py:883–894` | Last carry address, or incoming carry for an empty block |
| `HornerCarryCell.advance`, `hornerCarryAdvance` | mathematical model of `_shared/luo_core.py:882–894` | Pure carry and operand-dressing recurrence, without running a program |
| `HornerCarrySweepReady`, `HornerCarryEraseReady` | preconditions for those sweeps | Cell distinctness and clean carry scratch on the pure recurrence; erase readiness additionally reserves the external control |

## Proved

- The CCX fan updates the output by XOR with the selected multiplicand, keeps
  the phase and all other bits, and restores the complete state when repeated
  in the same increasing order. On zero target its value is the selected input.
- The quantum carry cell has an exact whole-state forward formula and an exact
  forward/backward formula, for both values of the sum and retained-carry flags.
  Measured release restores the phase for every tape.
- A forward sweep equals the pure carry recurrence and preserves phase.
- A release-only sweep with no retained top carry restores the complete original
  state. Forward and backward tapes may be chosen independently. The emitted
  backward program performs measurements and corrections, rather than reversing
  a list containing measurements.
- Exact counts: a forward sweep on n cells uses n Toffoli gates and no measurements;
  backward uses n Toffoli gates when sums are enabled, zero otherwise, and
  n measurements minus one when a nonempty block retains the highest carry.
  The empty-block subtraction uses natural subtraction and therefore remains zero.

## Still to prove / integrate

| Obligation | Status |
| --- | --- |
| Derive recursive readiness from distinct logical ports and initially zero carries | Proved; concrete arena placement remains pending |
| Whole-block arithmetic with controlled sums and retained top carry | Proved for the two sweeps, with arbitrary independent measurement tapes |
| Keeper placement, carry recomputation and keeper erasure between blocks | Pending |
| Truncated comparator, windowed correction, and actual `gc_lazy_cma` | Pending; no replacement with an ordinary controlled adder |
| Correspondence with `fusedLazyAdd` / `FusedAddGood` and their sufficiency | Pending |
| Complete halve-Horner / `row_mul`, s2 and s6 operand binding | Pending |
| Delayed unpark, measured endpoint lifecycle, concrete E contract and whole-machine 935 bound | Pending |

These modules keep all geometry and scratch hypotheses explicit. They neither
assert a physical 935 placement nor introduce numerical failure probabilities.

## Whole-block arithmetic and assumptions

`hornerCarryBlock_run` identifies the complete actual state after the two
sweeps with the pure descending recurrence. Its entry assumptions are global
port distinctness (including control and incoming carry) and initially zero
carry scratch. `hornerCarryFinishReady_of_advance` derives the intermediate
carry relations, rather than assuming correctness of an executed program.
The phase is preserved for every pair of tapes. This sufficient geometry
requires the incoming carry to differ from the external control. The author's
subtract spelling uses `cin0 = ctrl`, so that alias requires a separate
weaker-geometry theorem before inverse addition can use this interface.

`hornerCarryBlock_value` proves that the target word is
`(target + addend + cin) % 2^n` when sums and control are enabled, and is the
original target otherwise. `hornerCarryResult_top` identifies the retained
physical highest carry with the mathematical carry of the original words.
`hornerCarryBlock_fullValue` combines the actual low output and retained high
carry into the full integer sum. The addend and all other bits are specified
by the whole-state recurrence. For an empty block the high port means the
incoming carry; no new wire is allocated.

This is the full-width integer-addition stage inside the author's
`kb_ctrl_add_flag` (`_shared/luo_core.py:1043`), not the complete flag-writing
program. The flag toggle between sweeps, block keeper propagation/erasure,
`kb_fold_const` correction (1150), and `kb_lt_flag` comparison (1106) still
need composition. Consequently it establishes the low modulo-2^256 sum used
inside `fusedLazyAdd`, but does not yet prove the subsequent conditional
constant correction or the sufficiency of `FusedAddGood` for `gc_lazy_cma`
(1341). No canonical-mod-p adder has been substituted.

## Alignment with the three fused calls

The logical ports here must be placed according to
[FUSED_CALL_LAYOUT.md](FUSED_CALL_LAYOUT.md): scan control is a bit of
post-closer/repack `R[:256]`, target is the accumulator `out`, and addend is
`y`. Carries and keepers must use the actual 24-bit `P` allocation; this
arbitrary-list theorem does not allocate one carry for every bit of the
256-bit word simultaneously. The future block composition must prove its
own reuse schedule within that pool.

There is no arithmetic/layout discrepancy requiring a changed lift or fold:
lift reference 1–58 maps to `R[:58]`, pool 281–304 to `P`, and fold carry 536
to `P[0]`, not a separate seam carry. None of those reference addresses is
asserted to be a fixed caller wire in this PR. Actual repack-log selection
and injective placement remain caller obligations.

At s2 the output is A and multiplicand is y1; at s6 recompute the output is
y1 and multiplicand is the already rider-scaled A. s6 erase starts from a
parked folded row, so it cannot reuse a fresh signed-lift entry condition.
The descending carry sweep here includes measured release; it is not a
reversal of a measured gate list or a proof of inverse Horner. HMR's zero
basis word and its remaining phase debt stay separate until the lifecycle
proof establishes recomputation and the actual conditional phase correction.
