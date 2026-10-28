# Windowed slot through freeze processing

The emitted `RoutedBankLayout.windowSlot` now prepares activity and branch controls, performs routed arithmetic, resizes the four signed rows, updates the counter with borrowed scratch, retires the swap bit from the updated coefficient, and runs the blocked zero-test and freeze/offset program. `windowSlotInverse` reverses these stages using the separately proved inverse programs.

`windowSlot_spec` relates the actual program to `pinStep`: all four signed row values, the signed counter, the frozen flag and the offset register agree. It preserves phase, clears activity, swap and post-processing flags, and returns the free arena clean. The branch parity remains available for subsequent history transport. `windowSlot_roundtrip` restores the complete state for independently chosen forward and reverse measurement tapes.

The post-stage readiness proof derives clean workspace from the exit arena rather than assuming arbitrary scratch values. Persistent record and frozen wires must belong to the original live allocation and remain outside arithmetic targets. The layout, emitted resize plan, reserve result, signed numeric windows, counter fit, and branch nonzero/invariant hypotheses remain explicit theorem premises.

This is a single physical slot. It does not yet include history push/measurement and branch recovery, instantiate the finite 533-step walk, produce the controlled 257-bit inversion endpoint, prove a numerical failure bound, or establish the global 935-wire point-addition bound. In particular, the temporary physical views required by depth decoders must still be allocated when a public row window is narrower than those views.
