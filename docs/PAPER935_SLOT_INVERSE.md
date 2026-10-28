# Measured slot inverse and branch partition

`PostInverse` implements the inverse of the actual freeze/offset stage. The
controlled equality test is run a second time with fresh measurement outcomes;
its work returns to zero. The original fire flag is reconstructed from the final
frozen flag and offset, the latch is undone, and the zero predicate is cleared.
The early, unarmed stage only reverses the measurement-free activity retirement.

`RetiredSlotInverse.retiredSlot_roundtrip` composes this program with the measured
arithmetic body inverse. It restores the complete state, including phase, for
arbitrary independent forward and inverse tapes. Static wire separation, zero
work, physical row encodings, row/counter fit, and the actual divsteps invariant
remain explicit premises. The additional `hremint` premise is static separation
for the final offset comparator; no correctness oracle is introduced.

`BranchAssembly` proves two arithmetic/Boolean facts for the next history step:
finite depths 2 through 6 and the stored cutoff partition the nonswap class,
including a zero coefficient; the negative-counter decoded branch, swap bit,
and newly fired freeze assemble the original branch. The latter theorem keeps
an explicit successful-first-termination condition. A missed earlier termination
is not ruled out by the physical layout.

This PR does not yet compose the measured branch-history push/forget with its
full reverse reconstruction. It does not supply a width-changing finite walk,
a controlled 257-bit XOR inverse endpoint, numerical event bounds, or a global
935-wire allocation. The slot round trip is a component result.
