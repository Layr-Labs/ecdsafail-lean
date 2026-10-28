# Wide signed coefficient: mathematical range reduction

This change proves a mathematical transformation, not a circuit that produces
the transformed register. It selects no endpoint route and allocates no hosts.

Let p = 2^256 - (2^32 + 977), and assume |z| ≤ 2^280. For a = |z|, split
lo = a mod 2^256 and hi = floor(a / 2^256). The proved bounds are lo < 2^256
and hi ≤ 2^24. Define t = lo + hi * (2^32 + 977).

`wideMagnitudeFold_decomposition` proves the exact identity a = t + hi*p.
`wideMagnitudeFold_bound_le` proves t < 2p. The full high contribution is retained;
there is no truncation of a low-word overflow and no probabilistic escape.
This mathematical result does not validate the author's truncated row_reduce
program or remove its failure event.

For nonnegative z, `wideSignedFold z` is t. For negative z, it is zero when
t = 0 and otherwise 2p-t. The zero case prevents the excluded value 2p.
The result is a natural number strictly below 2p and has the same value as z
in ZMod p. `wideSignedFold_signed_le` proves the same facts for either +v or -v
from the explicit magnitude bound on v.

`fold32PlacedReduce_wide_input_le` connects this mathematical value to the
existing physical bounded reducer, provided the caller has ALREADY encoded
wideSignedFold z in its mapped data register. It discharges the reducer's
range premise and proves canonical output congruent to z, pool cleanup,
comparison behavior, control preservation and phase preservation. It does
not produce or assume proof of a physical folding implementation: the
encoding equality remains an explicit precondition.

The inclusive bound is essential: 280 payload bits plus a sign bit encode
[-2^280, 2^280), including -2^280 whose magnitude is exactly 2^280.
At this endpoint, hi = 2^24 and lo = 0, and the folded value still lies below
2p. The original strict-bound theorems remain available; the `_le` versions
cover the full representable interval.

`WindowRow.value_natAbs_le` derives the inclusive magnitude bound from signed
row semantics. `compileAuthorWalk_exit_fv_natAbs_le` specializes it using the
actual compiler's proved exit payload width 280, for every basis state and
conditional on successful compilation. `compileAuthorWalk_exit_fv_fold`
then discharges the mathematical signed fold's bound for either sign.
No arithmetic endpoint invariant or exclusion of the minimum value is needed.
These statements describe the existing row value, not a new encoded register.

Outstanding obligations include obtaining the magnitude/sign representation, implementing the
wide fold with full-state/phase and overflow accounting, producing the stated
encoding, preserving enough information for reversible cleanup, assigning
hosts/ownership, and connecting the endpoint. The existing exact bounded
reducer and its inverse do not discharge these obligations. No numerical
failure bound, new failure event, or complete 935-wire resource bound is
claimed. task #37 remains incomplete.
