# Conditional HMR row-multiply consumers

For the one-page handoff, see [Producer checklist](HMR_PRODUCER_CHECKLIST.md).

These interfaces implement the task #49/#50 → #51 agreement. They are
parameterized certificates, **not instances for the source circuit**. No
axiom, admitted theorem, or placeholder implementation is introduced.

## Producer obligations

`HmrRowMulLayout` names a 280-bit signed row, 256-bit multiplier and output,
24-bit anc pool, and extra comparison/flag scratch. It records widths and
separation. It does not assert that the HMR compiler reaches these views.

`HmrRowMulSpec L H` requires the actual program to begin with the existing
placed lift and fold, followed by the producer's scan/halves program. Its
execution field proves output `call.beforeSign`, unchanged multiplier and
sign, the row parked in the actual lift/fold representation, clean scratch,
and a precise Boolean phase-debt equation. The debt is a function of the tape,
absolute cursor and input state supplied with its execution proof. It is not
a caller hypothesis that phase is correct. Record legality is explicit through
`legalCursor`, so a fixed recorded program is not required to work with its
record references arbitrarily shifted. This contract alone does not construct
a typed quantum circuit or prove the ordinary gates have no aliases.

`HmrRowMulInvSpec` and `HmrRowUnparkSpec` are distinct: erase restores the
original signed row and zeroes out; unpark restores the row using the demolished
multiplier word and preserves out. Their input relations take the original
state, actual current state, global tape and cursor. The producer must prove
those relations at the actual lifecycle boundary. Their execution fields expose
phase debt; global cancellation is still a lifecycle obligation.

## Proved consumers

`hmrRowMul_consumer` derives lift encoding and the fold input magnitude from the
physical signed row and allocator readiness, then consumes the producer output
postcondition. `repacked_hmrRowMul_consumer` executes the actual swap journal
first and derives the coefficient equation from the original signed row.
`s2_hmrRowMul_consumer` and `s6_hmrRowMul_consumer` specialize to the pinned source
journals. No independent scanWord premise is added. Source-view identification,
input values and successful allocation remain explicit.

The unpark/erase consumers use the state after the intervening program and
advance the absolute cursor by its actual measurement count. They preserve the
phase-debt equation rather than silently replacing it with phase restoration.

## Three-call ownership schedule

`HmrArenaLease.release` derives exact return to the original arena and readiness
from successful reservation, support and actual final zeroes. It does not assume
a release postcondition. Existing data/output wires are never reserved again.

`hmr_s2_release` retains anc across forward multiply, HMR/corrections and unpark.
`hmr_s6_release` retains one anc lease across apply, corrections and erase.
`hmr_three_call_schedule` composes these two leases around an explicit
`HmrArenaTransfer` for the intervening caller segment. All states and tape
cursors are those of the concatenated execution. It derives both releases,
final readiness, and the two live-set increments of exactly 24 wires.

This is a **conditional schedule**, not the concrete source allocation trace.
The actual support/reservations, transition precondition/readiness, unpark and
erase preconditions, and new `compileHmrWalk` row addresses remain producer
obligations. No old 907/28 or 620/315 layout is used, and no whole-circuit 935
resource conclusion is claimed. Forward scratch cleanup does not cause an
early release before the end of a lease.

## Exact phase composition

`HmrLifecyclePhase.lean` defines `hmrPhaseDelta` from the actual run result of
a segment. This does not assert that any correction is effective. Its append
and three-segment laws use each preceding output state and the absolute cursor
advanced by `recordedMeasurementCount`; the tape is never restarted.

The s2 and s6 phase theorems are separate. Each combines the producer's forward
debt, the actual HMR/correction segment's phase change, and the unpark/erase
debt. Each has an exact `restored_iff` theorem for equality with the input phase.
The necessary and sufficient remaining equation is that the middle segment's
actual phase change equals the XOR of the forward and final debts. There is
no assumption that the middle segment preserves phase. Deferred Z and CZ
correction lemmas evaluate their contributions as the stored outcome AND the
current recomputed data bit(s); legality of record indices remains separate.

Basis postconditions are stated separately for s2 and s6. A restored row or
zero output does not establish phase cancellation. Concrete programs, producer
Spec instances and lifecycle input relations still need implementation; the
new cancellation criterion is not a proof that the source meets it.

The whole-caller theorem `hmr_three_call_phase` now consumes both forward
Specs, the s2 unpark Spec and the s6 erase Spec at the actual intermediate
states. It derives the phase of the same concatenation used by
`hmr_three_call_schedule`. Its `hmrThreeCallDebt` combines the s2 lifecycle
debt, the actual intervening caller's phase change, and the s6 lifecycle debt.
`hmr_three_call_restored_iff` identifies full phase restoration with this debt
being zero; `hmrThreeCallDebt_zero_iff` exposes the remaining source equation.
In particular, separate zero debts for s2, J and s6 are not required: their
contributions may cancel across boundaries. The producer instances and the
concrete cancellation equation remain open; this is not a RecordedAgreement
or a proof of the point-addition permutation.

## Lifecycle input relations

`HmrLifecycleInput` derives the producer `pre` predicates from explicit basis
boundary facts and a separate producer input rule. The parked boundary tracks
the original sign, the actual placed lift/fold payload and clean scratch.
Unpark additionally requires the demolished multiplier word to be zero; erase
instead requires the original multiplier bits and the forward output value.
The rule's record predicate relates the original and current absolute cursor.
Its `accepts` proof must be supplied by the producer: the old arbitrary `pre`
is not assumed to follow automatically from basis facts.

`hmr_unpark_input` and `hmr_erase_input` consume forward execution, actual
post-state frame/zero facts and the rule to conclude `unpark.pre` / `erase.pre`
themselves. For s6, instantiate the original input with the actual s2+J output
and the cursor advanced by its full measurement count. The basis frame permits
phase-only corrections on those wires; it is weaker than support disjointness.
No phase restoration follows from these input relations. Actual rule instances,
frame/zero facts and record predicates are still source implementation work.

`HmrLifecycleFrame` supplies sufficient facts from actual recorded instructions.
`hmrBasisWrites` tracks ordinary targets and measurement targets, excluding
control wires and all phase correction operands. It is not quantum support
and must never be used as a resource count. The frame theorem therefore allows
record-controlled Z/CZ on retained rows. `hmrDemolish_basis` proves destructive
X measurement sets the whole word to zero on all tapes; no phase claim is made.
The tail-zero theorem allows subsequent phase corrections while forbidding
ordinary writes to that word. The two input corollaries consume these facts
to conclude the producer `pre` predicates. Source program decomposition, write
footprint exclusions, record validity and actual input-rule instances remain
explicit, separate obligations; a recomputation that temporarily writes a
retained wire may instead use the earlier, weaker final basis-frame theorem.

## Connecting the nine-event budget to call inputs

`HmrGoodInput` consumes the same combined bad set as the symbolic budget.
`HmrCallBinding` records only physical coefficient/multiplier equalities and
zero output/scratch. Given an enabled call in the original label's modeled
call list and absence from the combined bad set, `hmr_pre_of_not_bad` derives
LiftGood/RowGood/HornerGood and hence the physical call precondition, while
retaining SignGood separately for later sign correction.

`hmr_reached_call_output` applies this at the actual state after a prefix P
and advances the absolute cursor by P's measurement count. It proves the H
output is exactly `call.beforeSign`; it does not replace that value with a
canonical residue. Call-list membership, enabledness, physical binding and
legal cursor remain explicit obligations, including when P is s2+J. This
bridge neither selects an input law nor discharges whole-program
RecordedAgreement or the concrete source producer instances.
