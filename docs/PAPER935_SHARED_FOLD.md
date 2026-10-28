# Actual shared-pool 58-bit fold

`Fold16Program.fold16Program` compiles the author's five-block fold using
control wire 0, data wires 1–58, and exactly sixteen pool wires 59–74.
The source partition is `[7,14,13,12,12]`. Each of the first four blocks
moves its terminal carry to the lowest newly occupied pool position using
three CX gates; the final block does not retain its terminal carry.
Reverse-order keeper erasure uses the source comparator construction and
measurement corrections, with scratch borrowed above the remaining keepers.

`fold16Program_contract` proves, for every initial state with all sixteen
pool bits zero and every measurement tape:

* the output word is `(input + selected literal) mod 2^58`;
* the selected literal is zero when the control is false, and otherwise
  `2^32+976` for addition or `2^58-(2^32+976)` for subtraction;
* all sixteen pool bits return to zero;
* the control bit and phase are unchanged.

No assumption supplies intermediate carry values, comparator predicates,
or successful cleanup. `Fold16Invariant` derives them from the actual
intermediate states. `Fold16Value` proves per-block integer conservation;
`Fold16Word` telescopes the actual saved carries into the full word result.
`Fold16Cleanup` composes the forward and reverse sweeps with their actual
measurement-tape offsets. The terminal carry of the final block is only a
mathematical witness to modular arithmetic, not an extra allocated wire.
`fold16Program_physical` proves ordinary gate legality and
`fold16Program_support` bounds every referenced wire below 75.

This is a complete reference-address fold component, not a complete
935-qubit inverse or point-add implementation. Embedding into the 256-bit
coefficient register, parity creation/erasure, the 498-step seam and
conditional rider schedule, and global live-resource composition remain
separate work. Its unconditional modular-word theorem does not remove the
explicit `FoldNoBorrow`/`AuthorScalingNoBorrow` premises required to identify
the truncated operation with ideal modular halving. No numerical failure
probability is asserted here.
