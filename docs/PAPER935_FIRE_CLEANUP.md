# Derived fire retirement

FireCleanup.lean closes the retained-fire cleanup predicate for the local
freeze latch. Before armed step t, FreezePin's invariant gives
offset <= t-Tmin < t+1-Tmin, and an active lane has offset zero.
After the latch, fire therefore equals
(zeroWitness AND recordEqualsCurrentOffset) AND frozen.
An earlier frozen lane cannot collide with the current offset. The physical
theorem derives this identity from freezeLatch_run; it does not assume fire
is independently known to be safe to erase.

eraseAnd uses an X-basis measurement and the outcome-conditioned CZ correction.
For either outcome it clears the target, preserves phase, and preserves all
other bits under the derived AND relation.

fireCleanup computes zeroWitness AND recordEqualsCurrentOffset using the
existing equalConstant circuit, erases fire with eraseAnd, then repeats the
comparison to clear its witness. Each comparison also restores its own work.
The full-state theorem holds for arbitrary measurement lists and leaves only
fire changed to zero. freezeLatch_cleanup composes it with the physical latch,
deriving the cleanup predicate and passing through scratch cleanliness.
Explicit nonaliasing, zero scratch, and width premises are retained.

This implementation recomputes the comparison, unlike the author's F16
retained comparison trail. Its actual costs are 2n Toffolis and 2n+1
measurements: 12 and 13 for six record bits. These are not asserted to be
the author's optimized costs. The support theorem includes both comparison
inputs and all work wires; containment in the 935 arena is conditional on
their declared membership, not a full live-allocation schedule.

The zero witness still needs production and retirement from the actual g row.
Intervening F8-F15 stages must preserve the witness relation and provide the
required clean scratch at F16. The reverse fireR comparator, full measured
trajectory, global 935-wire bound, and numerical failure bound remain open.
Results use the existing basis/phase interpreter with arbitrary measurement
outcomes; no new amplitude-level semantics or Framework spec adoption is
claimed here.
