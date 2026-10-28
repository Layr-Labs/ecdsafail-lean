参考宽度 1029 线，不是 935 布局方案。

# Reference endpoint normalization

`seedNormalize q row U p` is an actual program which forms a canonical field
word from a signed source row. It replaces a mathematical read with executed
gates, but **does not close the compact 935-line implementation**: the reused
`ModUnaryLayout` alone has `4*n+5` wires, hence 1029 for n=256, before source
rows. `seedNormalize_layout_size` proves this size. No full point-call binding,
quantum budget, numerical failure mass, or whole-program resource bound is
claimed here.

## Program and contract

The program temporarily complements every source bit under q, executes the
existing `Divsteps.endpointSigned` canonical reduction, adds 1 modulo p under
q using `Divsteps.endpointConstant`, and repeats the complement to restore the
source. Complementing a signed word gives `-v-1` even at its minimum value;
this avoids imposing a new signed-negation overflow restriction.

`seedNormalize_run` requires:

- the unary layout widths and distinct wires;
- a distinct signed source word, disjoint from the unary layout;
- q outside both the source word and unary layout;
- 1<p<2^n, initially zero U.z and U.work.

For every measurement tape its postcondition is:

- phase unchanged;
- U.z is the canonical residue of `if q then -row.value else row.value`;
- U.work zero;
- every bit outside U.z restored, including source bits and q.

`seedNormalize_bank` sets q to the actual f sign bit and row to the actual fv
row. Given the endpoint fact `f.natAbs=1`, it derives the output value
`endpointSeedRead p bank before.basis` using the physical sign-bit semantics.
It does not take a seed-value equality as a premise.

`seededAuthorWalk_normalize` applies that circuit to the **actual output
state** of `seededAuthorWalkProgram`. The existing endpoint theorem supplies
f=±1, and `seededAuthorWalk_seed_read` identifies the computed value with
`scaledInverseSeed p (input x)`. The unary layout's zero-output/zero-work
premises explicitly refer to that actual endpoint state. This theorem does
not infer layout allocation or readiness merely from an unrelated clean
input or from the mathematical seed definition.

## Interface to the scaling stage

The normalization postcondition is `regValue U.z = S(d)` with work and phase
restored. `seedNormalize_low_word` converts any result below 2^256 into
`U.high=false` and `regValue U.low=S(d)`. Thus the next stage must use exactly
these low 256 wires in the same output state, after a proved relocation to
its layout. Its additional pool/parity wires must be proved zero in that
state. The current normalization frame can preserve such wires when they
are outside U.z and were already zero.

The shared arithmetic premise is `AuthorScalingNoBorrow` (and its decomposition
`authorScalingNoBorrow_parts`): first 498 seam halvings, then rider activity,
with the rider starting at the seam output. No new seed reset or different
input distribution is permitted. Lamport owns the actual fold/seam/rider
interfaces and overall placement. The handoff names are `foldSeam_contract` /
`foldSeam498_correct`, `foldHalve_contract` / `foldHalve_correct`, and
`foldRider_contract` / `foldRider_correct`. These interfaces are under development
in his branch; this PR does not claim their composition. They require 17 actual
zero auxiliary wires, with the high zero bit preserved separately.

The compact allocation must start from `walkExitBank walkSeedBank slots`,
`walkExitArena walkSeedArena slots`, and `walkExitRecord [] slots`.
`seededAuthorWalk_run` supplies exit `Arena.Ready`. Only
`arenaWires \ exitArena.live` is available to borrow: zero-valued live rows,
records and controls still needed for reverse execution cannot be retired merely
because their values are zero. The planned scaling placement preserves the
entire exit live set plus the 256 output wires; the 17 scaling auxiliaries must
be reserved outside that set. Their availability still needs a proof. The rider
alive control is planned to use `walkRegisters.active`.

## Remaining physical obligations

This reference program establishes actual canonical register formation with
restoration, independently of compact placement. It does not supply a placement
within the remaining live-wire budget; its current layout is already too large.
A compact implementation must refine the same state contract with a suitable
allocator and prove its own physical gate validity/resource result. Full
inverse compute-copy-uncompute, all four point-level invocations, and the
cleanup after scaling remain separate obligations. The four rows in
`SCALING_CALL_SEEDS.md` therefore remain open for the compact call sites.

`seedNormalize_counts` gives exact Toffoli and measurement counts
`(row.payload.length+2)*(4*n-1)` for this reference construction. Temporary
complement gates are Clifford. This count is not an estimate for a future
compact replacement.
