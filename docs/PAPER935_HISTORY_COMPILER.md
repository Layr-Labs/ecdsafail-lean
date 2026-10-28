# Actual growing history compilation

`compileGrowingHistory` grows the actual history register before push, then borrows
one shared detector pool. The emitted `storePushForget` receives exactly that
grown register. Its length is `max requestedCapacity previousRecord.length`;
capacity is not silently replaced by a request or an empirical stack bound.
The counter detector and coefficient detector reuse their scratch sequentially.

The compiler contracts prove actual view identities and derived clean scratch.
Execution theorems prove the finite stack update, branch clearing, the precise
measurement-dependent phase, frame preservation, and clean pool release back to
the post-growth arena. `compileGrowingHistory_fit` connects absence of the declared
trajectory history failure to the actual finite push premise.

`compileHistoricalSlot` appends this stage to the public arithmetic slot. It takes
six coefficient bits directly from the actual exit row and checks their layout;
its selector and depth-7 correspondence are proved from the physical row encoding.
The history stage restores `SlotRegisters.Values` for the next slot. The additional
`compileCheckedHistoricalSlot` checks physicality and arena support on every emitted
history instruction and proves these properties, plus measurement-record well
formedness, for the combined emitted program.

All results retain successful-compilation, input encoding, numerical push-fit and
stated ownership/separation premises. The combined compiler requires a sufficiently
wide physical coefficient row; early short rows need real sign padding in the
future schedule. The compiler does not silently manufacture those bits. Reverse
history recovery, successful compilation and semantics of all 533 slots, the compact
inverse endpoint, the whole-machine peak and numerical failure probability remain
separate work. This is not a complete 935-qubit certificate.
