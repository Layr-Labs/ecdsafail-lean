# Actual history decoder and walk reversal

The decoder is now constructed from each actual `HistoricalSlot`. On the
existing `authorTrajectoryEvents` good-input event, the full 533-slot walk
followed by its constructed reverse restores the entire `State` (basis and
phase), for every measurement tape. `seededAuthorWalk_actual_reverse` includes
real initialization and cleanup. Neither theorem assumes `HistoryUndoAt`,
`WalkHistoryUndo`, or correctness of a supplied decoder.

## Exact theorem premises

`seededAuthorWalk_actual_reverse` quantifies over a finite original label type,
a mathematical input map, one label, any global tape and any original/reverse
cursors. Its remaining hypotheses are:

1. `p : Nat`, `p < 2^256`, and `(p : Int) % 2 = 1`.
2. The original label is outside `(authorTrajectoryEvents input p).bad`.
3. `seedBefore.Ready s.basis` and `(regValue seedG s.basis : Int) = input x`.
4. `compileAuthorWalk = some slots`, identifying the actual returned slot list.
   This is not a numerical success oracle: the already proved
   `compileAuthorWalk_exists` supplies such a list independently of the input.

There is no primality assumption, nonzero-phase assumption, decoder-success
hypothesis, or assumed per-step history recovery. The conclusion is a round
trip, not a claim that its endpoint is an unscaled modular inverse.

## Physical construction

`compileSlotDecoder` starts from the slot's **grown history arena** and
`slot.front.exitBank`. Later slots have already been undone when this decoder
runs, and the current slot's arithmetic has not yet been reversed. Sign padding
extends f to at least 6 payload bits and fv to at least 12, while retaining the
persistent history record. Five depth layouts (2 through 6) are compiled against
one eleven-wire borrowed pool.

The six-bit offset comparison uses the first six wires of that same pool and
restores them before lookup. Fire, active and sigma use retained, clean
`F.work0`, `F.work1`, and `F.swap`; they are not newly allocated free wires.
The geometry, cleanliness, comparison restoration and lookup availability are
proved from the actual compiler result. The lookup restores its pool, the
control cleanup restores those three retained wires, and reverse padding
restores the original bank. Only the forgotten branch port is toggled.

`decoderOffset i = max 1 (i+1-498)` handles the undetected early prefix without
a zero comparison threshold. Record bounds follow from `pinWalk_record`.
The existing no-early-zero condition supplies the nonzero predecessor required
for the first freezing step. No new numerical success event is added here.

## Composition and resources

- `compileHistoricalSlot_history_undo` combines actual decoder execution,
  original-record phase cancellation and history pop, at arbitrary original
  and reverse cursors.
- `compileHistoricalSlot_static_history_undo` supplies its input from actual
  arithmetic execution and proves the original history register was preserved.
- `compileHistoricalWalk_history_undo` follows the actual successive forward
  states and arenas. All static geometry, allocation and decoder success are
  derived; numerical inputs remain explicit at this general layer.
- `compileAuthorWalk_history_undo` derives the numerical inputs from the
  existing four-event good set. `compileAuthorWalk_actual_reverse` combines it
  with the already proved arithmetic inverse.
- `authorDecoderBudgets` checks the complete actual capacity schedule in the
  Lean kernel. `compileAuthorWalk_decoders` proves compiler success for every
  returned slot. `compileAuthorWalk_decoder_support` bounds every full decoder
  program's addresses by the 935-wire arena, including padding and cleanup.

The resource statements are distinct:

1. **Address support:** every instruction of each complete actual decoder
   uses only `arenaWires` (addresses below 935).
2. **Decoder allocation budget:** at each slot the compiler proves
   `historyArena.live.card + padding growth + 11 ≤ 935`. This includes the
   currently retained registers and grown persistent history. There is no
   additional six-wire comparison allocation: those six sites are the same
   pool sites, used earlier in time. This is a decoder-phase allocation result,
   not a composed peak theorem for the entire reverse/scaling/point-add circuit.
3. **Reuse semantics:** comparison restores all shared pool sites before lookup;
   lookup availability, retained-control cleanliness, noninterference, and final
   restoration are proved from compiler geometry and the actual forward state.
   They are not premises of the author round-trip theorem.

The optional `[]` failure branch in `actualHistoryDecoder` is never used for
an actual compiled author slot: success is proved separately and used in the
semantic proof. Measurements are not assumed uniform, and phases are not
assumed zero at intermediate boundaries.

## Remaining boundaries

This proves actual decoder support and full walk round-trip semantics. It is
not a proof of the entire inverse/scaling/point-add circuit's 935 peak, nor a
physical modular scaling endpoint, numerical failure probability, or complete
point-add implementation. Those conclusions still require their own physical
composition and resource proofs.

The physical scaling rider's low-window no-borrow condition is outside this
walk-recovery result. Its proposed fifth failure class has **mass pending**;
this result does not claim any total epsilon covers that extra condition.
