# Exact fresh isolated output capacity: zero

`retainedOutputSpace_empty` and `retainedOutputSpace_card_zero` prove that the fresh output space defined in the capacity certificate is empty, for every modulus parameter, original record ordinal, and successfully compiled author walk. `retainedOutputSet_empty` consequently proves that any proposed O contained in that space is empty.

The space excludes both the persistent exit live set and the actual return program's quantum support. The earlier bound of at most 28 is valid but not sharp: all 28 exit-free addresses occur in the return support. The proof does not evaluate an enormous emitted circuit or use an external execution as an oracle.

## Proof chain

1. `counterLiveCounts` records the scalar counter allocation sizes along the public schedule. `compileHistoricalWalk_counter_cards` proves this list equals the counter-arena cardinalities of the actual returned slots, using the compiler's real reserve operations and resize/history cardinality theorems.
2. `authorCounterFull` uses kernel evaluation only on this scalar schedule to prove that 935 occurs. `compileAuthorWalk_counter_full` obtains an actual compiled slot whose counter arena equals the entire 935-address arena.
3. `AllocationSupport` proves that each address removed from an arena by row resizing occurs in an actual emitted resize gate. It also proves that every allocated counter scratch site occurs in the actual counter inverse, using the exact ripple-adder support theorem. These are lower bounds on actual gate support, not merely allocator metadata.
4. `HistoricalWalkCompiled.reverse_coverage` propagates those facts through the real slot sequence: every site's ownership at a counter stage is accounted for by the final live set or actual reverse support. The decoder can be arbitrary; inverse arithmetic alone suffices for this coverage.
5. The full counter arena witnesses coverage of every arena address. Hence no address is simultaneously exit-free and untouched by the return program.

These theorems use successful compilation as a premise, as do the existing realized-walk certificates. No new probability assumption, trajectory condition, modulus bound, axiom, or gate-list reversal of measurements is used for the zero-capacity conclusion. The reverse is the existing measured reverse with original saved-record indices. Only the already-proper resize gates use list reversal.

## Scope for endpoint design

The output interface in `PAPER935_OUTPUT_SLOT.md` requires a **newly reserved** O outside the exit live set and all return support. For the current walk this implies O is empty; the interface cannot deliver a nonempty fresh retained output, even a single bit.

This does not rule out an output in a host that is already owned and live at the exit, because that host is excluded from the definition of fresh output space. It also does not rule out a different return program or a semantic preservation theorem allowing temporary touches. Each alternative needs its own actual wiring, writable-ownership, phase, and output-preservation proof. No such placement or alternative implementation is supplied here.

In particular, the theorem does not establish that the author's fused endpoint or an inverse-plus-Montgomery endpoint is impossible. It establishes that neither can use this fresh, syntactically isolated output interface to carry a nonempty result through the current reverse. Consuming an inverse before reversal still leaves the separate obligation to preserve the consumer's result.

The separate [owned-host output certificate](PAPER935_OWNED_OUTPUT.md) now proves actual support isolation and retained ownership for the existing `aHost` and a conditional output-preserving endpoint composition. It does not change this fresh-space theorem or instantiate the endpoint arithmetic.
