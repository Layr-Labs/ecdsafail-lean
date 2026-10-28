# Static success of the growing history compiler

`compileGrowingHistory_exists` proves that the actual history compiler returns a
layout when its persistent input addresses are distinct and owned by the input
arena, the counter sign is a view of that counter, and the arena has capacity
for the new history cells and the shared detector pool. Its exact capacity
premise is

```
A.live.card + (capacity - record.length)
  + max counter.length (coeffBits.length + 2) ≤ 935.
```

No execution result or arithmetic correctness premise is used. The proof follows
the two real allocator calls, constructs the actual detector views, and derives
the checked layout conditions from address separation. Sequential detectors
reuse the same pool; their views are not required to be mutually disjoint.

`HistoryLayout.support` and `compileGrowingHistory_support` bound every emitted
quantum address, including measured branch erasure, by the actual detector arena.
`HistoryLayout.Valid.physical` derives ordinary gate legality from the layout.
Consequently `compileHistoricalSlot_checked` proves that the final resource
checks succeed from persistent input ownership.

`compileCheckedHistoricalSlot_exists` combines these results with the existing
arithmetic slot compiler. Given a successfully compiled arithmetic slot, a
nonempty counter, an exit coefficient row of at least eight wires, separated and
owned persistent history inputs, and the capacity inequality, the full checked
historical slot exists. The six-bit selector and signed counter decompositions
are derived from those physical row lengths.

This removes the history compiler success premise locally. It does not prove
that the arithmetic slot compiler succeeds throughout the concrete 533-step
schedule, nor the whole walk's arithmetic and history-value invariant. The
reverse history compiler, inverse endpoint, full point-addition peak bound, and
numerical failure probability remain separate obligations. Runtime compilation
of the full schedule is not used as a proof.

The seven modules are exported through `ECDSAAdd.lean`; their public theorems are
included in the exact axiom audit in `scripts/verify.sh` with the existing whitelist
and verification limits unchanged.
