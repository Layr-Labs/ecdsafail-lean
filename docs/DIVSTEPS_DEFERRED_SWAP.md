# Deferred swap measurements on the physical walk

`DeferredSwapWalk.lean` replaces retained swap controls with actual forward X
measurements and reverse reconstruction throughout a finite physical walk.
It uses the existing gate programs and explicit absolute measurement ordinals.

For each step, the program executes:

1. The actual forward divstep, producing its three branch controls and data.
2. A bare X measurement of that step's swap wire, resetting it to zero and
   leaving the corresponding outcome-dependent phase.
3. The remaining forward steps and their reverse steps, recursively using
   the same deferred-swap construction.
4. One Toffoli to reconstruct swap from the retained activity control and
   the restored updated coefficient bit fv[1], followed by the phase correction
   controlled by the original forward measurement outcome.
5. The actual inverse divstep, including cleanup of the reconstructed control.

The reverse decoder handles frozen steps explicitly: activity is false and
swap reconstructs as false. The coefficient bit lemma covers signed words,
including the two-bit layout case. The stronger forward-step theorem exposes
all three actual control values while preserving the earlier public API.

## Proved contracts

`deferredSwaps_correct` proves complete state restoration for this same nested
recorded program, arbitrary incoming phase, every tape and every starting
cursor. Each recursive gap is the concrete later physical program; its
identity/phase behavior is proved by induction rather than assumed.
`deferredSwaps_wellFormed` proves that every record reference is to an earlier
measurement. No inverse measurement replaces the original recorded outcome.

`deferredSwaps590_correct` specializes the proof to 590 slots, widths
258/592/11, every odd nonnegative modulus below 2^256, and canonical inputs
0 ≤ x ≤ p, with the existing explicit layout and history-capacity hypotheses.
It requires no assumption that g is zero at the endpoint.

The exact complete-round-trip costs are:

- `N(2(5n+5v+k−4)+1)` Toffolis;
- `N(2(4n+3v+k−5)+1)` measurements;
- support contained in the original explicit allocation `L.used`.

At 590 slots with widths 258/592/11 this is 5,023,850 Toffolis and 3,321,110
measurements. Compared with the coherent forward/inverse pair, this adds one
reconstruction Toffoli and one swap measurement per slot.

`SwapHistory.lean` also includes the intermediate contract for a single swap
measurement spanning an actual coherent suffix walk and its inverse, along
with the reusable signed bit, phase-recovery and past-history freshness lemmas.

## Scope

All swap histories are measured; activity and parity histories remain
coherent. The layout still assigns distinct physical swap addresses, so this
change does not establish a smaller static allocation or any net resource
improvement. The follow-on [shared-swap schedule](DIVSTEPS_SHARED_SWAP.md) supplies that
separate layout and actual reuse proof; this file describes the original
distinct-address schedule.

This is a round-trip contract, not a complete modular division provider. It
does not supply deferred parity recovery, compressed activity history,
reverse scale removal, full point-addition integration, or a complete
590-step termination certificate. The shared checklist's parent items remain
open.
