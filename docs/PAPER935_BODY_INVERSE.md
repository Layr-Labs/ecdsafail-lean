# Actual inverse of the measured arithmetic body

`retiredBodyInverse` remints the swap tag from the retained old activity and the updated coefficient's second bit, then runs the actual inverse counter, row arithmetic, routing, branch tags and activity preparation. `retiredBody_roundtrip` restores the entire input state, including phase and all work wires, for arbitrary independent forward and inverse measurement tapes. Active and frozen lanes are both covered.

Measured programs are not reversed gate by gate. Each inverse row remints the AND removed by the forward measurement, reverses only the proper measurement-free arithmetic core, and performs a fresh measurement with its correction. `measuredAnd_roundtrip` proves this construction, and `branchRow_roundtrip` instantiates its witness from the actual arithmetic program. The pair, row stage, routed stage, active step and tagged/slot body theorems compose these concrete programs.

`retiredBody_roundtrip` derives the swap remint witness from the existing physical output-row encoding and the mathematical swap-bit law under the divsteps invariant. It assumes explicit layout separation, clean work, represented input rows and successful row/counter bounds, rather than assuming an inverse-circuit correctness contract. Frozen lanes require the established zero-g invariant.

The inverse has exactly one more Toffoli and one fewer measurement than `retiredBody`: reminting the retired swap uses a CCX in place of its forward measurement. Temporary row-AND corrections use fresh inverse tape positions. The original branch measurement's phase is handled separately by the history decoder.

This closes the arithmetic body round trip, not the whole inverse walk. The surrounding freeze post-stage, stored/decoded branch recovery and width-changing layout transitions still need to be composed. A concrete controlled 257-bit XOR inverse endpoint, global gate/record legality, numerical failure bounds and the 935-wire peak remain outstanding.
