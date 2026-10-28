# Physical history recovery and cutoff binding

`HistorySlot` proves that the actual retired arithmetic body and complete retired slot leave `parity = decide (bbit st = 1)`. The branch is the post-routing parity; it must not be replaced by old `g % 2` in the swap case. The slot theorem uses the actual post-stage frame and requires the parity wire to avoid the freeze-index register.

`StorePop` implements store-flag computation, the actual reverse brigade, and store-flag recomputation. `storeHistory_roundtrip` proves full-state identity after push then pop, with independently arbitrary measurement tapes on the two legs. `storePushForget_pop_stored` includes the forward branch measurement on selected lanes: the freed port was zero, so the outcome creates no phase debt and the actual pop restores the entire original state. Counts and support are explicit; the selector uses the existing per-bit comparators.

`HistoryPredicate` binds the actual coefficient input slice (bits one through the cutoff minus one) to integer divisibility. It derives the omitted low bit from coefficient evenness, handles the zero coefficient explicitly, and proves the stored class excludes swap when the cutoff is at least two. A negative-counter nonstored lane has nonzero coefficient with valuation in `[2, cutoff)`, the exact range needed by finite reverse decoding.

These results do not yet compose the complete slot and history segment, implement all reverse arithmetic or finite-depth decoders, construct the full inverse walk, discharge dynamic fit premises, or certify a 935-wire peak or numeric failure probability. In particular, the stored-path recovery theorem does not cover the nonstored branch-measurement phase; that requires its actual reverse decoder.
