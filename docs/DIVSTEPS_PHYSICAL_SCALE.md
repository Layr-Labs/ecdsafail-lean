# Physical activity-controlled scale removal

`WalkActivity.lean` proves the retained activity bits written by the actual
coherent forward walk. Every completed slot's history lies in later layouts'
past storage, and later steps preserve it. Consequently the physical control
wires read in reverse order contain exactly `reverseActivities p x N`; this
list is not an external assumption.

`PhysicalScale.lean` executes the existing `reverseHalf` gate program for each
of those physical controls. Frozen slots leave the modular accumulator alone;
active slots halve it modulo the odd modulus. The full sequence restores its
work registers, preserves phase, and preserves every bit outside its target
word, including the activity controls.

## Same-program contracts

`L.walkAndScale N U p` is the actual coherent forward walk followed by these
inverse-order controlled halvings. `walkAndScale_remove_scale` proves that its
canonical scaled accumulator becomes the desired field element. The theorem
requires the following explicit contracts:

- A valid walk layout, enough history slots, and all per-slot numeric fits.
- The initial walk encoding and clean work/history state.
- A valid modular accumulator layout disjoint from each controlling activity bit.
- A canonical accumulator value r and clean accumulator workspace at the end
  of the forward walk.
- A first stopping index t≤N, nonzero g before t, and g=0 at t.
- The scaled relation r=target·2^t in the prime field and nonzero field element 2.

The physical activity values are derived from the forward program. The
stopping and scaled-value premises remain mathematical obligations; no
endpoint g=0 conclusion is inferred from a fixed slot count. The final phase
is the initial phase, and the accumulator workspace is zero.

`walkAndScale_frame` additionally proves preservation of all walk wires when
the accumulator target is disjoint from the walk allocation. This provides a
frame for later uncompute; this program does not itself execute that uncompute.
The follow-on [scale/unwalk composition](DIVSTEPS_SCALE_UNWALK.md) supplies
that complete measured program and its restoration proof.

For walk widths n/v/k and modular-halving width parameter a, exact counts are:

- `N(5n+5v+k−4) + N(3a+2)` Toffolis;
- `N(4n+3v+k−5) + N(2a)` measurements.

These include every frozen slot. Support is contained in `L.used ++ U.wires`,
so qubit count is at most the sum of their lengths. These counts and support
belong to `walkAndScale`; they are not resource claims for the separate
shared-swap recorded round trip.

## Scope

This is the physical scale stage with proven activity inputs. It does not
construct or copy the scaled endpoint into the accumulator, prepare its input
state, establish termination, integrate scale into the measured shared-swap
reverse schedule, erase the remaining activity/parity history, or provide the
complete modular division or point-addition operation. No 2,613-wire or net
resource target is claimed, and parent checklist items remain open.
