# Static success of the actual 533-slot compiler

`compileHistoricalWalk_static_exists` proves that the actual list compiler returns
a slot list from initial address separation/ownership and a recursive predicate
on public numbers. The predicate tracks only row widths, live-wire count and
history length. It contains no compiler result or input-state execution oracle.

`probeChunks_count` proves the count of the actual tail-recursive chunker;
`postPoolSize_public` therefore expresses the shared post pool solely through
public input and offset lengths. `postViews_geometry` and
`historyViews_geometry` select their addresses from the full persistent layout.
`compilePublicSlot_static_exists` and `compileHistoricalSlot_static_exists`
combine the actual front, post and history planners. The disabled post path
requires neither a probe-width nor an offset-fit condition.

`planHistoryGrow_frame` and `compileHistoricalSlot_exit_geometry` return the grown
record and full persistent layout for the next actual compiler call. Detector
scratch is not retained in that arena. Exact row resizing and history growth
account for the next live count. This proves the recursive compiler exists by
induction over requests; the budgets remain sufficient, explicit public
inequalities rather than assumptions about execution success.

`authorHistoricalBudgets` checks those inequalities for the actual 533 author
requests in the Lean kernel. Seed geometry instantiates the general theorem in
`compileAuthorWalk_exists`. `authorWalk_realized` then gives the actual compiled
533-slot recorded program a `Circuit 935` representation for any initial record
ordinal. Neither statement assumes the compiler succeeds. Here “unconditional” means
there are no hypotheses: `compileAuthorWalk_exists` takes no parameters, and
`authorWalk_realized` takes only the arbitrary starting record ordinal. The
proof uses symbolic derivations and kernel `decide`, with no `native_decide` or
verification-limit changes.

The 935 bound here covers addresses of the emitted forward walk, including its
measurement instructions. It does not assert the arithmetic/history-value
invariant, correct inverse endpoint, a complete reverse implementation, whole
point-addition peak, or any numerical failure probability. Counter/window failure
events remain relevant to the arithmetic input contract. Kernel checking uses the
existing limits; no `native_decide`, axioms or whitelist changes are introduced.
