# Physical row-window resizing

`RowWindowResize`, `RowAllocation`, `WindowAllocator`, `WindowRows`, and
`WindowBank` compile public signed-row width changes into actual gates in the
935-address arena.

Growth borrows the least free addresses and copies the sign into each new high
bit. Shrinkage applies the inverse sign copies before returning the high
addresses. `shrinkRow_values` derives that those addresses become zero from
the integer fitting the smaller signed payload window. No allocator operation
resets a quantum wire.

`Arena.borrowMany_capacity` characterizes successful batch allocation by
`A.live.card + n ≤ 935`. `planRowResize` records both the emitted program and
the new physical view. Its correctness theorem proves the requested width,
value preservation, ownership, and cleanliness of every free arena address.
Its locality theorem preserves every other initially live wire.

`planWindowRows` composes these transitions for a finite bank, checking initial
and final disjoint ownership as public compiler conditions. `WindowBank`
specializes it to f, g, fv, gv and the existing `RowWindow` schedule interface.
The bank theorem preserves all four encoded integers and every other live
register. The emitted stream has no Toffoli or measurement gates, is proper,
and has support contained in the same 935 addresses. Its reverse is proved an
exact full-state inverse with independent measurement tapes.

`CounterBorrow` allocates a zero source and ripple carries from the exit
arena, then proves that the actual measured update restores and returns this
scratch to exactly the original arena. Its capacity condition is
`A.live.card + (2*width-1) ≤ 935`; it derives physical separation from fresh
allocation. `WindowCounter` proves resize-then-counter correctness and its
full-state inverse, with the counter undone before inverse resizing.

`WindowRouted` names the before/after physical views of routed arithmetic,
including the rotated g view. It proves active arithmetic, frozen identity,
zero-value preservation under that view rotation, and the actual measured
inverse. `WindowStep` composes routed arithmetic, resize and counter, proving
four-row values, clean free addresses, actual counter bits and a full-state
inverse on independent tapes. `counterWord_pinned` lifts the emitted counter
bits to the signed pinned transition under its explicit range condition.
`WindowHeadroom` derives all add-stage intermediate ranges from the input
window, so these do not introduce a separate overflow event.

These results do not yet prove that every step of the 533-entry public table
compiles, or integrate tags, activity, history and freeze stages into a complete
finite walk. Compiler success and numeric target-window fit
remain explicit hypotheses. In particular the bounded support of resizing
alone is not the global point-addition resource claim or a numerical failure
probability bound.
