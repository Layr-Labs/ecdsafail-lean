# Actual fixed-width divstep slot

`Slot.slot` concatenates the physical activity mint, the existing tagged arithmetic, and the actual public post-stage. `slot_spec` proves, for every measurement tape, that all five signed rows, the frozen flag, and the stop record implement `pinStep`. The g output uses the rotated half-view of the same wires. Activity, zero flag, and fire are cleared; phase is unchanged, and every wire outside row/tag/record/frozen outputs is preserved.

The theorem takes concrete wire lists and initial signed row values. The zero probe reads exactly the post-arithmetic g half-view. The active case requires local signed fit bounds; the frozen case requires g=0 and executes the arithmetic identity. Initial branch tags, arithmetic work, and comparator work are clean. Post-stage scratch and record wires must avoid arithmetic outputs, and the post-stage preserves all row wires. These static exclusions and representation/fit assumptions remain explicit and must be instantiated by the allocator and trajectory proof.

`slotBody_counts` adds no Toffolis or measurements to tagged arithmetic. `slot_counts` adds zero post-stage cost before Tmin, otherwise 2*gWidth+1+2*recordWidth Toffolis and 2*gWidth+2*recordWidth+1 measurements. Support results expose the union of actual body and post-stage wires; they do not bound peak live space.

This component does not resize rows, store branch history across slots, construct the finite walk, uncompute the complete inverse, or establish a 935-qubit allocation or numerical failure bound. In particular, q/parity are retained outputs, so repeated composition still needs a concrete history lifecycle. The comparator uses per-bit workspace and is not the paper’s optimized blocked-zero circuit.
