# Author fold carry blocks

This extends the literal `_cf_fwd` / `_cf_bwd` cells to a complete carry block.
`foldBlock` emits the forward cell, recursively processes the higher bits, and
then emits the backward cell. A carry is omitted when both the literal bit and
incoming carry-wire presence are zero. Only the final carry may be retained.

## Proven execution and arithmetic

`foldBlock_run` equates the actual program to `foldBlockModel`, an independent
Boolean carry-propagation model. It restores the initial phase on every tape.
Its premises are exactly a duplicate-free list of the control, optional input
carry, and every cell's data/carry addresses, plus initially zero carry targets.
Data, control, input carry, phase and tape are otherwise arbitrary. The result
specifies every output basis bit, including retained and erased carry targets.

`foldBlockModel_value` and `foldBlock_run_value` prove that sum mode writes
`(oldData + controlledLiteral + inputCarry) % 2^width`. The former is a pure
model theorem; the latter executes the measured program and retains the same
explicit geometry and clean-target premises. `foldBlockModel_frame` preserves
all addresses outside the cells.

`foldBlock_forward_count` gives the exact Toffoli count, counting only the
non-omitted carry cells. `foldBlock_support` bounds all used addresses;
`foldBlock_physical` proves ordinary-gate nonaliasing from the geometry premise.
These are block-local resource statements, not a 935-qubit allocation theorem.

## Keeper arithmetic and remaining work

`foldKeeper_borrow` proves that subtracting the literal plus incoming carry from
the written modular sum detects the original overflow, for width-bounded data
and literal. `foldKeeper_controlled` gives the author's controlled form, with
an explicit premise that an inactive control has zero incoming carry. These
are arithmetic identities, not a proof of the physical keeper-erasure circuit.

The multi-block pool schedule, comparator-based keeper erasure, actual fold
half/rotation, physical rider, and final point-addition endpoint remain to be
connected. In particular this change proves no whole-program 935 peak.
The low-window no-borrow condition from `FoldHalfMath` is an additional input
event; its fifth failure-class mass remains undetermined. No total failure
probability bound follows from these block contracts.
