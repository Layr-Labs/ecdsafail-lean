# Scaling seeds at the four inverse call sites

This is a mathematical call-site ledger and an endpoint observation theorem.
There are currently **zero fully bound physical seed-register call sites**.
It does not instantiate a compact `PointInverseEndpoint`, prove a numerical
failure probability, or establish the 935-qubit peak.

For original label `(control, P)` and fixed finite point `C=(cx,cy)`, write
`X,Y` for the original coordinates, `a=(Y-cy)/(X-cx)`, and
`Xout=genericX X Y cx cy`. In an ordinary enabled addition the existing
closed XOR-inverse adapters have these calls:

| Site | Inverse input d | Other operand at invocation | Mathematical pre-seam seed |
|---|---|---|---|
| quotientCompute | X-cx | Y-cy | S(d) |
| quotientCleanup | X-cx | a | S(d) |
| productCompute | cx-Xout | a | S(d) |
| productCleanup | cx-Xout | a*(cx-Xout) | S(d) |

Here `S(d) = ((pinWalk 498 p d 533).rows.f * rows.fv : ZMod p).val`.
The numerator of the inverse operation is **1**. Both existing adapters call
`inv`, then a Montgomery core, then `inv` again. In the product adapter the
inner core divides by the computed inverse, but the two `inv` calls still
receive d, not its inverse. `InverseQuotientRecorded.states` and
`InverseProductRecorded.states` describe these operand transitions under their
supplied inverse contracts; the point-level argument sequence comes from
`ConditionalPointDialog.generic_true` and its disabled counterpart.

Disabled calls retain X,Y and are excluded from the event by their enabled
flag. An infinite fixed point has no call descriptor. Missing coordinates
use the same `(0,0)` default as the existing input maps, with the actual
ordinary-addition guard determining whether the call is enabled.

## Proven bindings (observations and input maps)

| Object | Checked result | Limit |
|---|---|---|
| Actual seeded walk exit f/fv observation | `seededAuthorWalk_seed_read` derives `endpointSeedRead = S(d)` from actual execution and row encoding | Observation is a mathematical function of two signed registers; no canonical output register is produced |
| Scaled inverse relation | `seededAuthorWalk_seed_relation` derives `S(d)*d = 2^(498+offset)` in ZMod from the physical endpoint congruence | Requires the stated trajectory-good, encoding, compilation and coprimality premises |
| quotient compute/cleanup input and enable bit | `inverseCallArgs_input` identifies both with existing `callInput` | Adapter correctness remains conditional on the supplied inverse contract |
| product compute/cleanup input and enable bit | `inverseCallArgs_input` identifies both with `productCallInput` | Same limitation; no compact endpoint implementation is asserted |
| Enabled inverse inputs | `inverseCallArgs_nonzero` uses existing point-domain nonzero theorems | No new distribution assumption |

`endpointSeedRead` is deliberately not `regValue` of an allocated seed register.
The proof does not assume the desired seed equality: it derives the observation
from `seededAuthorWalk_run`; the congruence uses
`seededAuthorWalk_scaled_inverse`.

## Physical seed-register gaps

| Call site | Remaining physical binding |
|---|---|
| quotientCompute | Implement canonical signed f*fv normalization into the actual pre-seam register, instantiate the compact closed XOR inverse and connect its layout to the adapter |
| quotientCleanup | Same construction plus its actual cleanup invocation, scratch readiness and restoration |
| productCompute | Same construction for the second denominator, with the product adapter layout |
| productCleanup | Same construction plus the second adapter's cleanup invocation and restoration |

These gaps must be closed by program semantics, not by adding an assumption
that a physical seed equals S(d). The current Montgomery wrappers are not a
935-qubit implementation. `scaledQuotientSeed` separately defines the proposed
fused seed `(numerator*f*fv : ZMod p).val`; **there is no implemented fused
quotient program here**, and that candidate is excluded from this event ledger.

## Fifth event on original labels

Each of the four named sites has its own `inverseCallInput`, `inverseCallSeed`
and enabled-filtered `inverseCallScalingFailure`. Its predicate is
`¬AuthorScalingNoBorrow p 58 (2^256-p) d S(d)`, covering the 498 seam calls
followed by the rider activities, with no intermediate seed reset.

`adapterScalingFailure` explicitly unions the two inverse instances for each
adapter. `pointScalingFailure_adapters` proves the four-site union equals the
union of those two adapter events. Only **after** this union,
`pointScalingExclusive` subtracts the existing four-cause bad set. Its
disjointness theorem allows the existing symbolic mass partition to apply.
All events remain on the same original `(control,P)` labels. There is no
averaging, independence assumption, or substitution of a uniform denominator
law. Repeated denominators do not remove the obligation to bind both physical
invocations. Numerical masses and actual seed-register binding remain open.
