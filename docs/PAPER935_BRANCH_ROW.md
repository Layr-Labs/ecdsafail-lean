# Shared-carry branch arithmetic

BranchRow.lean implements actual F4 row arithmetic using the author's
shared-carry (hybrid k=0) path. It uses the existing rowAdd and now includes
the physical carry-in seed/unseed gates.

For a routed source a and target b:
- compute u = swap AND parity in a clean bit;
- complement the target under u;
- add a plus carry-in u under parity, using one clean shared carry;
- restore the carry and measure-erase u with its CZ phase correction.

The unsigned result is b if parity is false; otherwise it is a+b when
swap is false and a-b when swap is true, modulo the physical word size.
The signed theorem proves the exact integer result under a bound on the
final result. It needs no separate bound on a negated intermediate and
covers the most-negative input representable in the word.
All source/control bits, both transient bits, and phase are restored.

branchPair executes this kernel for the integer and coefficient target
rows, reusing the same two physical scratch bits. It recomputes/retires u
per row, whereas the author retains one u across both calls. Actual cost
is therefore one extra Toffoli and measurement per pair relative to that
shared-u choice: [1+(3n-2)]+[1+(3v-2)] Toffolis and two measurements.
No width-sized mask or carry list is allocated.

branchPair_divstep connects the actual gate output to the integer zStep:
the integer target holds 2*zStep.g before halving, and the coefficient
target holds zStep.gv. The theorem requires routed input rows, the actual
swap/parity values, odd f, and signed result bounds explicitly. It proves
phase and every bit outside the two targets unchanged, including scratch.

This is F4, not the completed five-field step. Physical control generation,
conditional routing, the counter update, g halving, fv doubling, resizing,
history, and forward/reverse stage composition remain to be connected.
The support theorem permits arena containment but does not establish a
whole-machine live peak or a failure probability. The chosen rows must
include their sign and scheduled add headroom. Full-schedule proofs must
discharge the local bounds and clean/nonaliasing premises.
