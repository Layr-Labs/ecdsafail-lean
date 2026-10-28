# Physical keeper erasure

This change implements and verifies the author's `_clt_fwd_cin` /
`_clt_bwd_cin` comparator, including its conditional Clifford corrections.
It composes that comparator with the data complements and controlled keeper
toggle in `kb_fold_const`. No measured program is reversed gate by gate.

## Execution contracts

`foldCompareForward_run` writes the one-bit carry into a clean target without
changing data. `foldCompareBackward_run` erases that known carry and restores
the phase for every measurement tape. The optional missing input carry and
zero-literal omitted cells follow the source directly.

`foldCompareBlock_run` composes the forward sweep, controlled terminal-carry
toggle, and measured backward sweep. It changes only the designated flag;
all initially clean carry targets and the phase restore. Its premises are the
explicit duplicate-free address list and clean carry targets.

`foldKeeperErase_run` sandwiches that actual comparator between data
complements. The resulting flag toggle is exactly the control AND the borrow
predicate `sum < literal + incomingCarry` evaluated on the original state.
`foldKeeperErase_clean` clears a keeper already equal to that predicate. Its
premises are geometry, clean comparator carry targets, and the stated keeper
value; it assumes neither a correct comparator nor a whole-block oracle.

`foldBlockModel_top` identifies the actual retained carry with the pure terminal
carry. `foldBlock_keeper_predicate` derives its controlled borrow predicate
from `foldBlock_run` and the word-sum theorem; inactive controls must have zero
incoming carry. `foldBlockModel_carry_clean` identifies all nonretained targets
as zero. Moving a keeper into its pool slot and transporting this predicate
through the other blocks remain part of the multi-block composition.

## Resources and boundary

The complete comparator and keeper erasure have proved address support and
ordinary-gate nonaliasing. Their Toffoli counts are at most `width+1` and
measurement counts at most `width`. The erasure uses only the supplied data,
control, incoming carry, keeper, and comparator scratch addresses.

`FoldPoolPlan` records the author's 58-bit/16-wire block sizes
`[7,14,13,12,12]`. Kernel-checked arithmetic proves their partition and forward/
erase capacities. Forward scratch excludes earlier keepers; erase scratch also
excludes the current keeper. A retained terminal carry and its destination
slot are distinct. These are allocation-index facts; this change does not yet
compile and verify the complete five-block program or its reuse invariant.

The physical fold half/rotation, rider, and point-addition endpoint are still
being connected. A sixteen-wire plan is not a whole-program 935-qubit peak
proof. The shared fifth no-borrow event's numerical mass remains undetermined,
and this change claims no total failure probability bound.
