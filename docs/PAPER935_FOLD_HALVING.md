# Physical fold halving and seam

This extends the proved sixteen-pool fold to the author's 256-bit halving
stage. Reference addresses are parity work line 0, data 1–256, fold pool
257–272, and (for the controlled rider only) alive line 273.

`fold256Program` injectively relocates the pool above the data register.
It leaves the upper 198 bits unchanged. Its subtraction branch is exactly
`windowSubtract 58 (2^32+976)`, with no success-event premise. The even
literal preserves the original low bit in both directions.

`foldParityProgram` copies the low bit by CX, runs the actual measured fold,
and clears the copy by CX. `foldHalveProgram` then performs the source
adjacent three-CX swaps. `foldHalve_contract` identifies its unconditional
numeric result with `foldedHalf 256 58 (2^32+977)` and restores all seventeen
work lines and the initial phase for every measurement tape.
`foldHalve_correct` identifies that result with ideal `halveMod` only on
the explicit shared `FoldNoBorrow` event.

`foldSeamProgram n` actually repeats this program on the same work lines.
`foldSeam_contract` proves iteration of ideal halving under the matching
`ScalingNoBorrow` predicate for `replicate n true`; `foldSeam498_correct`
specializes the theorem to the author's fixed 498-call seam.

`foldRiderParityProgram` computes alive AND low-bit into the parity line,
runs the same fold, and measures the parity line with its CZ correction.
`foldRiderProgram` follows this with the actual Fredkin rotation from the
source. Its contract proves controlled `foldedHalf`; the ideal controlled
halving theorem retains the explicit active-call no-borrow premise. The
inactive theorem proves full-state identity, including phase and outsiders.
The alive bit is preserved, and all seventeen work lines return to zero.

Ordinary gate legality and actual instruction support are proved for both
stages and for the repeated seam. The reference support bounds (273 or 274
addresses) are local component bounds, not a global 935-qubit result. The
alive line is an input to the rider; no theorem here manufactures the
host reverse walk's activity bit or composes the rider into its decoder.

Still required for a complete compact endpoint: placement in the actual
live layout, physical normalization/seed formation, insertion into the
reverse walk at the author schedule, complete register cleanup, and global
live-resource and numerical failure-mass proofs. Mathematical seed
readout equalities and the explicit no-borrow premises do not discharge
those physical obligations.

The normalization-to-scaling interface supplied here is `foldSeam_contract`:
its input is the actual state `s`, with data `fold256Word`,
`Fold256Ready s.basis`, `s.basis 0=false`, and the matching
`ScalingNoBorrow ... (regValue fold256Word s.basis)`. The future normalization
program must establish those predicates (after a justified physical wire
placement) and its seed-value postcondition on that same state. No
normalization-program theorem is assumed or supplied by this PR; the
existing `seededAuthorWalk_seed_read` is a mathematical readout theorem.
The normalization workstream's named interfaces are `seedNormalize_bank`,
`seededAuthorWalk_normalize`, and `seedNormalize_low_word`. The last is
expected to supply the zero high bit and the low 256-bit value. These are
handoff names for future composition, not dependencies used to discharge
this PR's explicit preconditions. The current normalization reference uses
1029 wires and cannot be inserted into a 935-address layout.
