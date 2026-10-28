# Deriving decoder readiness from physical execution

`DepthLayout.Static` contains public alias checks and physical view shapes. `available_of_bank` derives all clean scratch values from free arena ownership and obtains signed inputs from the actual row bank and counter. `available_of_pin` selects the frozen case from the actual exit flag; an unfrozen exit necessarily came from active arithmetic.

`available_after_padding_mint` applies these results after the emitted row padding and actual history control reconstruction. Padding uses at least six payload wires for f and twelve for fv, retaining other row widths. Its numeric fit follows from each physical row's representable range. A retained owned wire outside the original rows cannot occur in padding support, which supplies the needed port/frozen separation.

`storePushForget_frame_arena` proves that actual history storage and branch measurement preserve the clean free arena when the history register and port are owned. `storePushForget_decoder_available` derives decoder availability after that actual forward execution, actual padding and actual control reconstruction. `storePushForget_ready_recover_pop` uses it for all five depth stages and restores the complete state. It no longer assumes a decoder `Available` oracle.

The public alias/view checks, concrete padding plan, free-region capacity and separation, incoming encoded `pinStep` state and numeric/history success premises remain explicit. The final theorem still receives control and record-value premises used by the phase-recovery interface. This is not yet a complete physical layout compiler, finite 533-step walk, inverse endpoint, numerical failure bound or global point-addition resource proof.

Decoder scratch (`cleanWires`) is taken from unborrowed free arena addresses, and its zero values follow from `Arena.Ready` (free implies zero). These addresses are within the 935-wire arena but are not counted in `A.live`. The complete step compiler and peak-resource ledger must borrow them or explicitly account for their use; this remains a caller obligation rather than a resource theorem proved here.
