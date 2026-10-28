# Compact row arithmetic and shifts

`Paper935.RowStage` composes the shared-carry branch pair with signed doubling of fv and signed halving of g. `rowStage_divstep` proves that the actual gate program produces the next g, fv and gv values of `zStep` on active lanes, preserves phase for every measurement tape, and restores every wire outside those three rows.

The theorem requires already-routed row values and physical swap/parity controls, odd f, clean two-wire branch workspace, disjoint registers and explicit signed-fit bounds. It does not yet derive controls or implement routing, the z update, freezing, resizing, or a complete walk.

Halving reads g through `skywalkHalfView`: the output view rotates the old low wire to the high end. The proved set equality ensures this relabelling uses exactly the same physical wires. Callers must carry the changed ordered view forward.

For g width n and fv/gv width v, the program uses `(1+(3*n-2))+(1+(3*v-2))+v` Toffolis and two measurements. The shift stage allocates no additional scratch. The branch pair still recomputes its conjunction once per row, as documented in PAPER935_BRANCH_ROW.md. Arena containment is conditional on the supplied physical layout; it is not a whole-machine peak-live bound or a 935-qubit certificate.

Public semantics, cost, support, and view-set roots are included in the exact-axiom verification script.
