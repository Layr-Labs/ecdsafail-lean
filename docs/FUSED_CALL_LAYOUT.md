# Fused calls: entry, exit and placement

Source: `andigu/uncompute@64b5a13aa249f1360846657392e6c66817b26d0f`,
`tasks/modinv-point-add/circuits/divsteps/circuit.py` (HMR, qcap=935, wide=False).
Shared component references below are in the adjacent `engine.py`. This is the source contract
for the three `FusedCallSites` labels; caller invariants below still need Lean
binding. Addresses are logical wire lists, not an asserted fixed 935-wire map.

Let `R = inv.walk.fv.ids` **after closer/repack**, `s = fv.sign`,
`P = ma["anc"]`, and `C` be the signed endpoint coefficient. Here `R` has
280 payload bits, `P` has 24 clean bits, and the sign is separate. Closer
changes ownership and may repack wire IDs (1162–1178); do not identify `R`
with a contiguous portion of `x1` without proving that placement.

| Call / source | Entry to row_mul | Exit from row_mul |
|---|---|---|
| s2 quotientApply, 128 | `R` encodes `C` in two's complement, sign `s`; multiplicand `y1 = Y−Q.y`; output `A=0`, freed by closer. `mm.on(24,seam=True)` supplies clean `P` and one flag (126–127). | `A` contains the unsigned fixed-scale product, before sign_fix; `R[:256]` is the folded scan word, `R[256:]` remains the high magnitude, sign retained. `y1` unchanged; pool clean. **Row remains parked**, not restored. |
| s6 productRecompute, 181 | Signed `R` for the second denominator; multiplicand `A` is the product after walk-C's rider halvings, **not raw slope**. Output `y1=0` after its HMR, host use and closer; clean plateau pool (172–180). | Same parked folded row; `y1` contains unsigned fixed-scale product before sign_fix; `A` unchanged; pool clean. |
| s6 productErase, 190 | **Parked magnitude/folded `R`, not a new signed-lift input.** `y1` has been sign-fixed, phase-corrected, then inverse-sign-fixed (182–185); `A` is the same scaled operand. | Inverse fixed halves and inverse scan return `y1=0`; inverse fold borrows it, then inverse lift restores signed `R`, sign retained and pool clean (3286–3294). Any phase from the intervening correction belongs to the lifecycle proof. |

The two s6 model labels share one `FusedCall` (`fusedPointCall_erase`); this
identifies mathematical data, not identical physical entry states.

## Reference-to-caller maps

| Proven component reference | Actual role |
|---|---|
| lift `0`; `1+i` for `i<280`; `281+j` for `j<24` | `s`; `R[i]`; `P[j]` |
| fold `i<24`; `24+i` for `i<256`; `280+i` for `i<256`; `536` | `R[256+i]`; `R[i]`; borrowed zero word `Z[i]`; **`P[0]`** |
| Horner scan controls; multiplicand; accumulator | `R[:256]`; `y`; `out` (2999–3038) |

Thus lift's low window 1–58 is `R[:58]`; its 24-wire pool is exactly the
Horner pool, reused sequentially. Fold's carry is a pool bit, **not**
`ma["carry"]`: seam allocation leaves that single absent (2909–2923,
3312–3324). Injectivity/disjointness must hold within each component; the
sequential reuse of `P[0]` does not require an extra live wire.

## Borrow/restore boundary

Forward fold borrows `out` only before Horner starts. PR200 restores it to
zero before the first copy round. At s2, after sign_fix, HMR demolishes
`y1` (130); **that** zero word supplies deferred inverse fold in
`row_unpark(y1,ma)` (131; engine.py:3326–3333), then inverse lift restores `R` before
pool release and closer_inv. At s6 erase, inverse Horner first returns
`out=y1` to zero, and inverse fold reuses it. No forward call emits an
immediate unlift.

Proved component facts: lift magnitude under LiftGood; fold output under
RowGood; non-low frame, pool/word/carry cleanup and ordinary-gate legality.
Remaining caller obligations: actual row lengths and injective maps after
repack, signed input encoding, zero hosts/pool at each boundary, Horner's
output/cleanup, HMR phase correction, and complete lifecycle/935 support.
The row-fold output equals the model scan word via PR200's
`fusedRowFoldSource_of_good` and PR196's `FusedCall.scanWord_eq`.

## Lean boundary bindings

`FusedBoundaryLayout` reads the actual compiled endpoint row length (280)
and proves that an explicit relocation journal preserves this length and
distinctness. Finite lift and fold placements use list lookup; their
injectivity follows from row/host ownership and a successful 24-wire pool
reservation. Fold order is `R.drop 256 ++ R.take 256 ++ Z ++ P.take 1`.
The allocator has capacity for this pool after the compiled closer.

`FusedBoundaryZero` transports an explicitly zero initial A host through the
actual seeded walk and closer using their proven support exclusion. Actual
successful closer readiness and pool reservation imply every pool bit is
zero. HMR demolition clears every word bit for every tape, including an
absolute recorded cursor; an explicit repack transports those zero bits.
No HMR phase-restoration theorem is asserted here.

Still uninstantiated: the concrete journal chosen by the source closer's
`_repack()` (the existing Lean closer releases payloads but does not compile
that source selection), and the
three full caller programs. The maps are finite injective reference maps,
not yet complete renamed lift/fold executions. The s6 inverse-scan zero
boundary remains the Horner contract, not an assumption discharged here.

`FusedRepackAllocation` checks every journal move against actual ownership
and reservation. Accepted journals preserve readiness under their emitted
swaps; final ownership is exactly the initial live set under `repackEquiv`.
Owned row/host views therefore remain owned after the same moves. This
removes the need to assume the ownership transaction for a checked journal;
it does not supply the author's concrete journal selection.

## Pinned source journal

The selected entry is `circuit.py`, with `HmrDivstepInv`, 533 steps and
60 history bits. Its calls use `HMR_POOL_PLATEAU = 24` (engine.py:3492);
`HMR_POOL_PLATEAU_SEAM = 24` (3490) documents the alternative wide seam
where a host word remains live. The staged entry has the same arithmetic
flow at engine.py:3882/3936/3945, but a different allocation schedule.
Its addresses must not be used for this instance.

Run `python3.13 scripts/extract_fused_repack.py --source /path/to/uncompute
--output data/fused-hmr935-repack.json` on the pinned checkout. The script
executes the selected entry and observes the original closer/repack methods
without replacing their semantics; it stops after the second closer.
The JSON records ordered free lists, owners, row views, and actual swaps.
Builder allocation includes reserved but currently free home-band slots;
it is not the logical live ownership set used by `Arena.checkRepack`.
The export is evidence of source selection, not a Lean proof that the
compiled walk reaches those views or that its destinations are clean.

## Compiled walk parameter mismatch

The current `compileAuthorWalk` is not a gate-by-gate certificate for the
selected HMR entry. `HistoricalWalkCompiler.historyWindow` retains at least
seven fv bits, `walkRegisters` has a seven-bit counter, and
`AuthorDecoderUndo` uses threshold seven with decoder depths two through
six. The selected source HMR configuration instead has Wz=6, stores history
at j5p and decodes depths two through four. Its schedule tables were used
by the existing Lean instance, but those matching tables alone do not
establish matching compiler parameters.

The existing 907/28 and 620/315 bounds apply to that Lean instance only.
Before binding these concrete HMR journals to a complete caller, the walk
parameters and corresponding compilation certificates must be reconciled.
The source export, generic placement/zero lemmas and shared row arithmetic
remain usable independently; none discharges this missing correspondence.

## Checked source snapshots

`FusedSourceRepack` transcribes the source logical live sets (638 slots) and
the s2/s6 four-move journals. `check_fused_repack.py`, run by verification,
checks those constants against the pinned JSON export. The Lean proofs
establish successful `checkRepack`, distinct bounded swap endpoints, final
ownership under the swap permutation, and readiness after every tape.
Readiness is conditional on the initial source snapshot being ready. These
are concrete source-snapshot results; reaching these snapshots from the
compiled walk remains an independent obligation.

## Finite placement execution

`FusedPlacedExecution` turns the finite list placements into wire maps whose
default is unused on reference ports. Allocator-derived list injectivity
therefore supplies the finite injectivity needed by the actual interpreter.
For every tape the renamed lift computes the encoded coefficient magnitude,
restores its pool and sign, and preserves phase and outside wires. The
renamed source-order fold computes the full magnitude fold under RowGood
and restores every wire outside the placed low row, including the borrowed
word and carry. Signed encoding, initial clean inputs, and numerical good
conditions remain explicit physical preconditions. These results do not yet
derive them at the three complete point-add call sites.

`FusedPlacementViews` proves that the physical lift payload and fold
low-then-high payload are the same row in the same order. Its
`placedLift_fold_encoding` derives the fold's coefficient encoding from
actual lift execution; the lift pool's zero precondition follows from
arena readiness and successful reservation via `fusedPool_zero`.
`FusedPlacedInverse` proves full physical forward/inverse restoration for
both components and independent tapes. The inverse starts at the actual
forward output; this does not yet discharge the lifecycle invariant after
intervening Horner/sign/measurement operations. The borrowed zero word,
sequential pool release and complete call-site invariants remain to connect.

`FusedPlacedBorrow` derives the borrowed word's zero state from actual
measurement and proves that a disjoint renamed lift preserves it. This
does not erase measurement phase debt. The physical pool sites are restored
by the lift and the subsequent fold's carry is proved to be the cleaned
P[0]. A reservation/release theorem returns the lift's clean pool with the
original live set and readiness. It is an ownership contract, not an early
pool release inserted into the source program: release after the complete
Horner/unpark lifecycle and the exact call-site schedule remain open.

## Signed physical input bridge

`FusedSignedPlacement.placedMagnitude_encoding` derives the reference lift's
sign and two's-complement payload from `WindowRow.value` on the physical row.
`placedSignedLift_fold_encoding` composes this with the actual renamed lift,
using allocator readiness to obtain its clean pool, and establishes the fold's
magnitude input. The only arithmetic input equality is the physical signed row
value equaling the modeled call coefficient; `MagnitudeEncodes` is no longer an
independent premise at this boundary. Width, ownership, separation and
`LiftGood` remain explicit. Establishing that the source walk reaches this row,
and the Horner/unpark/s6 lifecycle, remain separate obligations.

`FusedRepackedInput.repackedRow_value` additionally proves that executing a
valid repack journal preserves the signed value when both payload and sign
views follow its permutation. The two pinned source journals have explicit
`s2RepackedMagnitude_encoding` / `s6RepackedMagnitude_encoding` corollaries.
These transport an existing physical signed-row invariant; they do not assert
that the compiled walk reaches the source snapshot, nor that an arbitrary row
parameter is the source's fv row. That source-view identification remains open.
