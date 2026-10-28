# Frozen-lane behavior of the compact step

`IdleRows` proves that the same compact measured program used for active arithmetic preserves the complete physical state on a frozen zero-g lane, for every measurement tape. `taggedStep_idle` includes branch-tag generation, routing, both measured branch rows, shifts and counter update. It assumes the active bit is false, g represents zero, tags and branch workspace start clean, counter workspace is zero, and the declared register/width conditions hold.

The proof does not delete the measured gates or ignore their phase effects. Each disabled branch row is a full-state identity for arbitrary measurement outcomes; the composed program restores phase and every physical wire. It does not require a signed overflow premise for a frozen lane.

The half step still changes the ordered g view used by the caller. `halfView_zero` proves the rotated view also represents zero, so physical-state identity and logical frozen-state identity agree.

A frozen lane is not free: this is the same static gate list with the same gate and measurement counts as the active implementation. The theorem does not derive the active bit from a freeze flag, implement the freeze latch or record lifecycle, compose public width changes, or prove a whole-machine peak-live bound. Those components still need to be connected to the finite walk. Earlier active-step resource caveats remain unchanged.

All nine public identity/view roots are exported and included in the exact-axiom audit.
