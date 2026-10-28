# History budget for the actual author walk compiler

`AuthorHistoryBudget.lean` binds the indexed failure-budget capacity to the
list-based capacity of `compileAuthorWalk` at each of its 533 indices.
`authorHistoryCapacityAt_eq` is deliberately restricted to `t < 533`: the list
lookup defaults to zero beyond the end, whereas the indexed recurrence continues.
`authorHistoryFailure_iff` proves that this difference outside the range has no
effect on the declared history failure event.

`authorTrajectoryEvents` fixes the original-label accounting to freeze threshold
498, depth 7, 533 steps, the compiler's actual history capacity, and the original
author row windows. The signed counter has seven sites including its sign bit,
as in `walkRegisters`; this is distinct from its six magnitude/payload bits and
from the six-bit freeze offset. Original row windows remain a conservative
failure condition even though physical coefficient rows are sign extended for
the history detector. This module does not prove full execution fits those rows.

`compileAuthorWalk_history_fit` applies to any actual returned slot. Successful
compilation and its slot index provide the real checked call, selector layout and
record capacity. The stored branch follows from metadata, actual wiring, and the
old row's odd `f`. Outside the four-event union on the same original input label,
the theorem supplies the finite push inequality. Its remaining state encoding,
row invariant and unbounded-stack value assumptions are exactly execution facts
that require the whole-walk arithmetic induction. The theorem does not derive
those facts from compiler success.

`authorTrajectoryBudget_total` gives the exact symbolic union mass under any
supplied input law. `authorTrajectory_mass_le_requests` transfers a bound proved
with the smaller per-stage requests to the actual retained capacities. The
resource result `authorHistoryCapacityAt_bound` (at most 60 bits) is not a bound
on overflow probability and is not used for that implication.

Concrete compiler success as a kernel theorem, the complete arithmetic execution
invariant, reverse recovery, inverse endpoint, actual per-call input laws and
nontrivial numerical probability bounds remain separate obligations. No sampling
result, numerical epsilon, or complete point-add resource certificate is asserted.
