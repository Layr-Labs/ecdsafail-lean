# Compiled history and the failure budget

`HistoryBudget.lean` connects the growing historical slot compiler to the existing
trajectory failure events. The capacity used at step `t` is the actual length
after growth, not the request at that step:

```
length 0 = initial
length (t+1) = max (request t) (length t)
capacity t = length (t+1)
```

`historyLength_eq` identifies any successfully compiled prefix satisfying that
recurrence with this mathematical schedule. It does not prove that every slot
compiles or that a complete schedule returns successfully. For example, requests
8 then 4 retain capacity 8 at the second step; a smaller request does not release
record bits.

`compileHistoricalSlot_trajectory_fit` specializes the existing growing-history
fit theorem to the actual historical slot. Its depth 7 and post-slot selector are
derived from the compiled six-bit coefficient view and encoded output state.
The stored branch is derived from the slot's output metadata, compiler wire
identity, and oddness of the old `f` row. The caller retains successful compilation,
arena ownership/readiness, actual row and metadata encodings, the current history
value, and the actual length recurrence as explicit premises. Outside the declared
history event, the resulting theorem supplies the actual finite push premise.
It neither assumes a physical selector correspondence nor proves the complete
execution invariant by itself.

`historyBudget_good` extracts that event exclusion from the existing four-event
union on original input labels. `historyBudget_total` gives its exact symbolic
mass under the supplied `InputLaw`, through the existing exclusive partition.
There is no assumption of independence, uniform arithmetic arguments, or uniform
measurement outcomes.

`HistoryFailure.capacity_mono` and `trajectory_mass_capacity_mono` show that larger
capacities can only reduce failures and their mass. In particular,
`historyCapacity_failure_subset` permits a strict bound proved using the smaller
per-step requests to cover the actual retained-capacity schedule. This does not
assert such a numerical bound exists: actual input laws, per-call argument maps,
strict counting or analytic bounds, full execution correspondence, successful
compilation of the concrete 533 steps, and the inverse endpoint remain separate
obligations. No numerical epsilon or whole-machine 935-qubit result is claimed.
