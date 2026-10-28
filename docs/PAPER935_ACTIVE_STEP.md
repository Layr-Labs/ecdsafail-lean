# Compact active divstep composition

`routedStage` physically swaps the f/g and fv/gv pairs before the shared-carry branch arithmetic and signed shifts. `routedStage_divstep` now takes the original four row values, instead of requiring callers to supply already-routed values. Its output is exactly the four row fields of integer `zStep`.

`activeStep` appends the existing signed counter update. `activeStep_divstep` proves all five output fields equal `zStep`, preserves phase for every measurement record, and restores every wire outside the four rows and counter. The g output uses the rotated half view from RowStage; the other register views are unchanged.

## Preconditions and remaining work

`taggedStep` additionally computes swap and parity from the original physical z sign and g low bit using the existing four-wire `branchTags` circuit. `taggedStep_divstep` proves the same five-field result from initially clean tag bits, eliminating the supplied swap/parity equalities. Odd f makes the original g parity equal the post-routing branch parity. It retains these two tags as outputs; their later cleanup and history allocation are not yet implemented here. Tag generation adds one Toffoli and no measurements or additional scratch.

These are active-lane circuit theorems. For `activeStep`, active is true; swap and post-routing parity controls are supplied as physical bits with explicit mathematical equalities. The theorem assumes odd f, non-overlapping registers, clean branch and counter scratch, and local signed-fit bounds for the g numerator, fv, gv and z outputs. `taggedStep` generates the tags but does not erase them; neither theorem covers frozen lanes or composes a resizing walk, inverse, or endpoint provider.

Counter width remains a parameter. For n counter bits the reused counter implementation reserves n zero-source bits and n-1 ripple-carry bits; the theorem does not claim that this is the paper's optimized counter circuit. Six bits are valid only when the explicit signed-fit assumptions hold; a failure-probability theorem is still required.

## Resources

For f/g width a, fv/gv width b and counter width n, routing costs a+b Toffolis. Row arithmetic plus shifts cost `(1+(3*a-2))+(1+(3*b-2))+b`. The counter adds n-1 Toffolis and n-1 measurements, for a combined 2+(n-1) measurements. Branch arithmetic uses its existing two scratch wires; routing and shifts add none.

The exact count and conditional arena-containment theorems are exported and audited. Arena containment assumes a supplied layout; it does not prove the existence of a live allocation for the whole walk within 935 qubits. See PAPER935_ROW_STAGE.md and PAPER935_BRANCH_ROW.md for the retained cost differences from the author generator.
