# Compiled public slot

`compileCheckedPublicSlot` emits sign padding, routed row arithmetic, exit resizing,
counter update, and an armed or unarmed post-stage. Before the freeze threshold,
the post-stage uses three ordinary gates and allocates no probe pool. Armed slots
borrow the shared probe/offset pool and return it clean.

`compileCheckedPublicSlot_run` proves that the actual emitted program implements
one `pinStep`, with unchanged phase and restored arena readiness.
`compileCheckedPublicSlot_roundtrip` proves exact full-state restoration by the
emitted inverse, with independent forward and inverse measurement tapes. Measured
programs use their proved inverse constructions, not gatewise list reversal.

Both results require successful compilation, input encodings, arithmetic invariant,
explicit numerical width bounds, and the stated address-only `MathChecks` and
post-stage separation premises. The compiler checks ordinary-gate physicality and
arena support; it does not yet discharge every mathematical-layout premise or prove
that every scheduled slot compiles. `compileCheckedPublicSlot_qubits` is conditional
on the supplied arena's capacity. It is not a complete 935-qubit certificate.

The output retains the old branch parity bit explicitly. History push/forget and
reverse recovery, the full 533-step compiler, the compact inverse endpoint, and
numerical failure probabilities remain separate work. No input distribution or
uniformity assumption is introduced here.
