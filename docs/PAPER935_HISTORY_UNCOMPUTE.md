# Measured history restoration

The inverse restores the branch that was actually measured before popping the
stored history. This order matters: on stored lanes the measured port was zero.
`branchRecovery_measured` derives the finite-depth, swap, and newly frozen masks
from the divsteps invariant and the explicit successful-first-termination
condition. Their XOR is exactly `!stored && branch`.

`finiteBranchProgram` executes the actual five depth decoders followed by four
gates adding swap and freeze contributions. `finiteBranch_cancel` then cancels
the old absolute-ordinal measurement phase. `storePushForget_recover_pop`
composes this concrete decoder with actual history push/forget and pop, restoring
the entire initial state and phase. Its storage predicate is derived from the
physical counter and coefficient prefix, including coefficient zero. It assumes
record capacity, clean work, layout separation, and physical swap/fire values;
it does not assume an arbitrary decoder's correctness.

`FrozenReady` supplies the alternative clean-layout contract for frozen lanes.
On those lanes the actual lookup is the identity, without requiring fictitious
updated arithmetic values. The finite chain and history round trip accept this
alternative alongside the active row encodings.

`mintHistoryControls` computes the new freeze flag from the final frozen flag
and offset equality, then computes old activity and swap from the updated
coefficient's second bit. Its inverse clears all these controls after the
decoder writes its separate output. `cleanBranchProgram` combines these actual
programs, and `storePushForget_clean_recover_pop` proves the full history round
trip without a precomputed swap/fire premise. Physical recorded-offset and row
encodings, a smaller previous offset, and clean work replace those premises.
The current comparator offset must be positive; an unarmed slot with record zero
can use positive dummy offset one, provided the physical offset word fits it.

Outstanding integration includes arranging physical views across the
width-changing walk, the controlled 257-bit XOR inverse endpoint, concrete
failure probabilities, and a global 935-wire allocation. These component
theorems do not establish those claims.
