# Fifth failure event: low-window subtraction

**第五类质量待定 / fifth-class mass pending.** This change defines the event
and its disjoint partition. It supplies no numerical probability bound and
makes no claim that a total epsilon covers physical scaling.

## Shared interfaces

All names are in `ECDSAAdd.Arithmetic.Paper935`, module `ScalingNoBorrow`.

- `FoldNoBorrow width c r` is exactly `r % 2 = 1 → c-1 ≤ r % 2^width`,
  the existing `foldedHalf_correct` premise. Physical callers should use this
  name rather than define a similar condition.
- `ScalingNoBorrow p width c flags seed` follows a mathematical recurrence:
  check the condition if the current flag is true, then update by `halveMod p`;
  false flags leave the value unchanged. Thus only active odd values can fail.
- `AuthorScalingNoBorrow p width c x seed` covers the 498 unconditional seam
  calls followed by `authorRiderActivities p x` (reverse indices 532–498).
  Its `seed` is the **pre-seam** value. `authorScalingNoBorrow_parts` proves
  the split: the rider starts at `(halveMod p)^[498] seed`.
- `foldedActive_correct` proves equality of the fold recurrence and ideal
  modular-halving recurrence under this condition. This is mathematical
  composition, not an assertion about an unproved physical circuit.

The author physical parameters are n=256, width=58, c=2^256-p. The general
correctness theorem retains the required positivity, oddness and literal-fit
hypotheses explicitly. It does not infer them from a name or a probability law.

## Original labels and physical binding

`authorScalingFailure input seed p width c : Finset X` takes two *mathematical*
functions on the same original finite label space X: the divsteps argument and
the pre-seam scaled quotient/product. Neither function takes an interpreter
state or a measured physical register as input.

The call-specific seed function must be instantiated with its mathematical
pinWalk/ZMod value when the actual quotient or product call is connected.
That instantiation is not supplied here: it depends on which arithmetic call
is using the inverse. Equality of the physical pre-seam register to this
mathematical value is a separate circuit-binding obligation on the existing
good set. The event must not be redefined in terms of that physical register.

For a fixed original label x, being outside this event is equivalent to
`AuthorScalingNoBorrow ... (input x) (seed x)`. A physical rider can use the
proved seam/rider split after its binding equality has been established.

## Disjoint fifth cell

For the existing four causes e and the raw scaling event S, the new union is
`scalingBad e S = e.bad ∪ S`. The fifth exclusive cell is `S \ e.bad`, appended
to the existing ordered four exclusive cells. `scalingBad_pairwise` proves
all five cells pairwise disjoint, and `scalingBad_partition` proves their union
is the new union. `scalingBad_mass` gives exact symbolic mass under the same
`InputLaw X`; it assumes neither independence nor uniform inputs.

Actual label-law instantiation, the call-specific mathematical seed, its
physical binding, and a numerical bound for the fifth mass remain required.
