# Actual HMR sign correction and lifecycle gaps

This task #58 increment proves the sign-correction cleanup and the basis-state
roundtrip in the actual s6 gap. It does not complete three-call integration,
phase-debt cancellation, point addition, or the whole-machine 935 bound.

## Source and replay

The source is `uncompute` commit `64b5a13aa249f1360846657392e6c66817b26d0f`.
The entry is `tasks/modinv-point-add/circuits/divsteps/circuit.py`, HMR935.
`capture_lifecycle.py` executes that entry and captures every emitted operation
between the first row multiplication and unpark, and between the second row
multiplication and inverse multiplication. It records absolute measurement
ordinals, the source hash, the actual ports, and sign-correction boundaries.
`data/hmr-lifecycle.json` retains the raw operations.

Run `scripts/paper935/generate_lifecycle.py --check` with Python 3.12 and
`ECDSA_PAPER_SOURCE` pointing to the pinned clean source clone. This is also a
required step of `scripts/verify.sh`. The replay must match both JSON and Lean
text exactly. This external replay binds the transcription to Python; Lean
proves the semantics of the transcribed instructions.

Normalization uses the already proved source conventions: a SWAP becomes
CX(b,a), CX(a,b), CX(b,a). Corrections immediately following an HMR and using
its own record become that measurement's correction list, in source order.
Remaining Z/CZ instructions retain their absolute record ordinal. The source
normalization lemmas are in `HmrSourceNormalization.lean`.

| Gap | Raw operations | Measurements | Start cursor | End cursor |
|---|---:|---:|---:|---:|
| s2 | 1488 | 340 | 251208 | 251548 |
| s6 | 2215 | 168 | 620177 | 620345 |

These cursor values are captured source positions. The generic gap theorems
hold for arbitrary cursors and tapes. They do not prove that a complete Lean
walk reaches those source positions.

## Proved conclusions

The sign core uses a 58-bit window, the exact constant `2^32 + 976`, and the
24-wire block plan `[14,22,22]`. The Sign24 files specialize the existing
FoldBlock proof machinery. Both window orientations restore scratch and
phase. The 256-bit CX fan and the outer `CX sv sf` pair produce the actual
sign-fix shape. Finite-support placement requires injectivity only on its 281
reference ports. The row-sign wire is outside those ports.

`HmrSignSourceBinding.lean` checks the three actual sign programs against the
placed core with `rowMulPrefixEq`. Its semantic proof permits CCX control
exchange and independent same-target CX commutation, rather than assuming
syntactic instruction equality. The checked equalities hold for the complete
state, every tape, and every cursor.

`HmrSignLifecycle.lean` proves:

- Actual s2 and s6 sign correction restore the 24 ancillary bits, f-sign, and
  incoming phase when those ancillary bits start zero.
- The complete s2 gap zeros the actual y word and keeps the ancillary pool
  zero. The source row payload and row sign are preserved by the separate
  frame theorem.
- The complete s6 sign / recorded-Z / inverse-sign gap restores **every basis
  bit**. The recorded-Z phase contribution is retained; this is not a proof
  that the s6 gap restores phase.

## Arithmetic output under explicit input premises

`signCore_value` proves the reference core's mathematical output under the
low-window no-borrow condition. `placedSignFix_of_good` transports that result
to physical ports and includes the actual outer CX pair.
`s2SourceSign_of_good` and `s6SourceSign_of_good` instantiate the exact source
programs, output words, ancillary lists, and f-sign wires (768 and 795).
Their result is `if call.negate then fold32Prime - call.beforeSign else
call.beforeSign`. These are conditional execution theorems; no row-multiplication
output encoding is assumed to have been proved.

## Remaining integration obligations

Structural scratch cleanup and the basis roundtrip do not require arithmetic
success. To use sign correction as the mathematical residue negation, callers
must still supply `call.SignGood`, the before-sign value encoding, and the
separate binding `call.negate = sf XOR sv` at the actual sign entry. No such
binding is inferred from row multiplication. The source-bound signed-output formula is now proved under these premises;
the preceding row-multiplication proof must still establish their applicability
at each actual call boundary.

The actual forward row multiplication, unpark, inverse multiplication, full
walk, intermediate program J, and complete phase-debt cancellation still need
their producer proofs and integration. This increment adds no admissions and
does not discharge those obligations in `WaitingOnProducer`.
