# Reverse recovery of a compiled historical walk

`WalkRecovery.lean` emits a reverse program for the actual list of
`HistoricalSlot`s. Each reverse stage performs branch recovery (including the
saved-record phase correction), history pop, then the actual compiled arithmetic
inverse. Stages are emitted in reverse list order. This is not reversal of the
forward instruction list.

For a slot starting at forward record ordinal `o`, its forgotten branch refers to

```
o + measurementCount (slot.program F) + measurementCount (storePush ...)
```

Here `slot.program F` is the arithmetic public slot; the historical slot adds the
push/forget stage. This source ordinal is computed in forward order and retained
unchanged in the reverse program. A separate reverse cursor advances by the
actual measurement counts of already emitted reverse stages. Both interpreters
use the same global tape so saved results are available; new inverse measurements
use the cursor after the complete forward walk. No distribution or uniformity
assumption is made about that tape.

`WalkUndoConditions` is a recursive specification of the **local** obligations.
The state supplied to its tail is exactly the execution result of the preceding
forward slot. Its head reverse cursor includes the count of the reversed tail.
Consequently the conditions cannot be satisfied using an unrelated collection of
states that do not join at stage boundaries.

The local interfaces have concrete constructors in `WalkRecoveryReady.lean`:

- `historyUndoAt_of_ready` applies the existing
  `storePushForget_ready_recover_pop` theorem with its original layout, padding,
  five-depth decoder, register-view, cleanliness, finite push, and numerical
  premises. It retains the original record ordinal and its phase cancellation.
- `slotUndoConditions_of_compiled` derives arithmetic reversal from
  `compileCheckedPublicSlot_roundtrip`, retaining the compiler equation,
  MathChecks, row and metadata encodings, ownership/separation, arithmetic range,
  and offset premises. The reverse arithmetic tape is arbitrary.

`HistoricalSlot.undo_run` combines these two local results.
`historicalWalk_reverse_run` derives full `State` equality by list induction, so
both the basis state and phase are restored. `historicalWalk_forward_reverse_run`
states the same result for the single concatenated forward/reverse program.
`compileAuthorWalk_reverse_run` specializes it to the actual returned 533-slot
list. Compilation success supplies that list and its length; it is never used as
an inverse-correctness premise by itself.

`WalkRecoveryRecords.lean` separately proves all saved-record reads are legal once
the forward walk has completed. It proves well-formedness of each inverse stage,
the whole reverse list, and the concatenated program for a successfully compiled
walk. These facts require no semantic local conditions because all old sources
belong to their already completed forward slot.

Remaining obligations are explicit. A caller must supply actual per-stage decoder
programs and establish the local readiness/encoding/range conditions on the actual
forward states (for every tape when an all-tape result is needed). This change does
not construct their whole-walk allocation, prove their 935-address support, bound
the inverse resource peak, establish the arithmetic execution invariant, prove the
concrete author compiler succeeds, or produce an inverse endpoint. It adds the
composition and record accounting needed once those conditions are available.
