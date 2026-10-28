# Actual lift-window and row-fold gate components

Author source: `andigu/uncompute@64b5a13aa249f1360846657392e6c66817b26d0f`,
`tasks/modinv-point-add/circuits/divsteps/engine.py` and
`tasks/modinv-point-add/circuits/_shared/luo_core.py`.

## Lift window

`Lift24Program.lean` implements the `kb_fold_const` operation called by
`engine.py:3296–3308`: controlled addition/subtraction of one on the low
58 bits, using the actual 24-wire pool. The author's `_plan(58,24)` yields
sizes `[14,22,22]` and starts `[0,14,36]`. There are two saved keepers;
the final block uses the remaining 22 pool bits. Keeper cleanup uses
measurements and record-dependent corrections.

Reference addresses are control 0, window data 1–58 and pool 59–82.
The program contract proves the exact word modulo 2^58, unchanged control,
zero pool, and phase restoration for every tape. The separately compiled
minus-one program undoes plus-one as a full ambient-state equality on a
clean pool, even on window-wrap inputs. Each direction costs 95 Toffoli
and 92 measurements, with support inside these 83 addresses.

`FusedMagnitudeProgram.lean` combines this subroutine with the sign-controlled
complement of the entire 280-bit payload. Its injective placement leaves the
low window at 1–58 and moves the pool to 281–304. The full source-order
lift/unlift pair has an ambient-state round-trip theorem on a clean pool,
95 Toffoli and 92 measurements in each direction, and support below 305.
`FusedMagnitudeValue.lean` additionally proves the forward magnitude formula
and derives the absolute coefficient value from the existing `LiftGood`
condition and an explicit two's-complement input encoding. It also proves
pool cleanup, retained sign and phase for this forward run. The window's
high-payload frame is proved from the physical support, so the value proof
does not assume that the other 222 payload bits stay unchanged.

## Row-fold stream

`FusedRowFold.lean` implements `engine.py:2948–2996` for high width 24 and
low width 256. Reference addresses are high 0–23, low 24–279, borrowed
word 280–535, and carry root 536. The initial copy accounts for tap zero.
The remaining taps are `[4,6,7,8,9,32]`; each actual Cuccaro addition
has a 25-bit accumulator and one zero padding bit immediately after it.
The normalized stream follows the central 256-bit addition by reversal of
the build. `FusedRowFoldSource.lean` additionally retains the author's actual
increasing copy-loop order at tap zero in both sweeps. It proves equality of
execution with the normalized stream on all states and tapes, and transfers
the full-state round trip, support, and counts to this source-order program.
The inverse replaces only the central adder with its literal reverse,
matching `_cdkm_sub`, not complement-add-complement subtraction.

Proved: proper gates, full-state forward/inverse round trip on every basis
state and every tape, support in 537 addresses, and 1086 Toffoli with zero
measurements in either direction. The separate sign is not in the support.
The round trip also covers dirty scratch and arithmetic wrap lanes.

`FusedFoldArithmetic.lean`, `FusedFoldTap.lean`, `FusedFoldBuild.lean` and
`FusedRowFoldValue.lean` prove the forward numerical contract. Starting with
a zero borrowed word and zero carry, the builder computes high*(2^32+977).
The running coefficient bound derives zero padding and nonoverflowing
25-bit additions at every tap; callers do not supply intermediate-state
assumptions. The central addition updates the low word modulo 2^256.
Commuting that low-word change through the inverse builder proves a full
ambient-state frame outside the low word, including phase, high payload,
borrowed-word cleanup, and carry cleanup. This holds on wrap lanes too.

`fusedRowFoldSource_of_good` proves that RowGood and an explicit magnitude
input encoding identify this actual low output with `wideMagnitudeFold`.
This is the gate-level counterpart of PR196's `FusedCall.scanWord_eq`:
under the same `RowGood`, that mathematical theorem identifies `call.scanWord`
with the same full fold. Thus the actual low output equals `call.scanWord`
by transitivity with `scanWord_eq.symm`; no new success condition is added.
`FusedMagnitudePhysical.lean` supplies ordinary-gate legality for the full
lift independently of its numeric success conditions. Enclosing caller
placement, lifecycle and a whole point-add peak remain separate obligations.

## Proven and remaining boundaries

| Component | Proven | Remaining |
|---|---|---|
| 58-bit ±1, actual 24-wire pool | Numeric word, clean pool, control, phase, all-state clean-pool round trip, physical gates, support and counts | Enclosing point-program placement |
| Full 280-bit magnitude lift | Actual complement/window order, forward absolute value under LiftGood and explicit encoding, pool/sign/phase, ambient round trip, gate legality, 305-address support and counts | Enclosing lifecycle and caller encoding binding |
| Actual row-fold source order | Forward folded word under RowGood, unconditional wrapped arithmetic and full non-low-word frame, high/word/carry cleanup, round trip, source equality, 537-address support and counts | Enclosing placement and caller encoding binding |
| Full fused endpoint | No completed claim in this change | Arithmetic composition, lifecycle, point-add binding, numerical failure mass and whole-program peak |
