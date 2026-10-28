# Exact incumbent port: recorded carry cleanup

The promoted full point circuit remains `adcdfef`: 2,223,041 static Toffolis,
1,561,029 measurement instructions and a certified allocation ceiling of
1,899 logical sites. Stages 2 and 5 use 1,056,832 and 1,056,833 Toffolis.
The recorded-circuit modules below are separate components and are not yet
used by the production point circuit.

The source being ported is `ecdsafail/ecdsafail-challenge` at
`9db31da9a0971a2185e54d12d9441c36838aba40`. Its normal `carry_step`,
`unwind_carry_step` and `rail_ripple` use both immediate measurement corrections
and corrections controlled by earlier measurement outcomes. The original
ECDSAAdd instruction language exposes only immediate corrections.

`RecordedSyntax` and `RecordedSemantics` add an explicit, immutable outcome
tape and absolute record ordinals. The original instruction language embeds
with identical complete-state behavior. `RecordedRelocation` proves closed
composition and correct record offsets. `RecordedWireRename` proves that
quantum placement preserves behavior and classical record identities.
These modules leave the original interpreter and protected point specification
unchanged. Old measurement records are classical data, not additional qubits.

`RecordedRailCarryProgram` copies the pinned normal carry/unwind gate order.
`RecordedRailCarryProof` proves restoration of source, carry-in, phase and
scratch, while updating the target sum bit. It distinguishes the original
outcome controlling the deferred Z from the independent fresh outcome
controlling the immediate CZ. The local compute/retire pair costs 1 Toffoli
and 1 measurement, with four quantum sites when a carry-in is present and
three otherwise. This is not the cost of a complete field cell or stage.

All seven modules passed isolated strict Lean checks on the CPU pod. Times
for syntax, semantics, phase example, relocation, quantum renaming, literal
carry program and literal carry proof were 2, 2, 8, 2, 2, 2 and 28 seconds.
Selected transitive axiom queries contain only `propext`, `Classical.choice`
and `Quot.sound`. These checks are not a new full-point verification.

The complete pinned Rust generator also builds in isolation. A full-width
reconstruction of its fused field cells emits 768 static Toffolis per cell,
but fails arithmetic or phase on explicit boundary inputs. It is rejected.
The post-fold comparison does not automatically reconstruct the original
carry predicate. Widening a seeded comparison also conflicts with the donor
fold layout. Neither this rejected cost nor any candidate qubit reduction
is included in production resources.

Remaining work is the complete native ripple, exact field fold and carry
recovery, interleaved lifetime placement, and integration into the original
all-valid-input point contract followed by full remote build and axiom audit.

## Complete native ripple certificate

The complete normal unsigned ripple now passes Lean for arbitrary aligned
widths, arbitrary input phase and all independent measurement outcomes.
Its saved-record phase debt is explicitly evaluated on the original operands.
The proof restores the source, carry-in, every spectator and all carry scratch,
while updating the target by unsigned addition modulo its binary width.
Numeric port alignment implies the recursive shape certificate.
Causal well-formedness and the actual quantum support are proved separately.
At width n it emits n-1 Toffolis and n-2 fresh measurements, with one carry
bank. At 256 bits its quantum support is at most 767 sites including input
ports. This is an unsigned component bound, not a Stage 2/5 Q measurement.

The full ripple proof passed in 4 seconds. The causal/layout certificate
passed in 7 seconds. Exact arithmetic mirror identities passed in 21 seconds:
adding the source to the complemented sum reproduces the original carry at
every binary prefix and returns the complemented original target. The full
chunked Defer/Apply gate composition and signed native tick remain to be proved.
