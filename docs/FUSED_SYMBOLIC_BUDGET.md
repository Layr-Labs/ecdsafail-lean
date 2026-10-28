# Symbolic nine-event budget

`FusedSymbolicBudget.lean` uses exactly the nine disjoint cells already defined
by `FusedFailureEvents`: counter, history, deadline, window, scaling, row,
lift, Horner, and sign. All are subsets of the same original input-label space.
The four fused events are aggregated over enabled modeled calls on each label;
replayed calls do not introduce independent random inputs.

`fusedExactBounds_total` identifies the sum of these nine exact cell masses
with the mass of the existing combined bad set. `fused_error_exact` then proves
the measured output error bound `2 * sqrt(total)` for any `InputLaw`, normalized
input amplitudes matching its encoded pushforward, and total below one.
The typed circuit supplies physical legality. The complete all-tape
`RecordedAgreement` outside the bad set remains an explicit hypothesis;
this theorem does not certify the unfinished point-add circuit by itself.
The mathematical ideal permutation is a separate argument, not extracted
from the implementation.

For later certified estimates, `FusedMassBounds` permits nine upper bounds
on these same exclusive cells. Nonnegativity of their total is derived from
the mass inequality. No independence assumption or numerical epsilon occurs.

## Empirical application (conditional)

Owner selected point-add-denominator-induced sampling and an explicitly
empirical table. See [ASSUMPTIONS_B5.md](ASSUMPTIONS_B5.md) for both assumptions,
precise original-point law, sample metadata, tables and limitations.
`FusedEmpiricalBudget.lean` wraps assumed population bounds with separate sample
metadata and reuses the symbolic theorems. Observations do not prove these
bounds; the original exact symbolic theorems above remain unchanged.

Actual circuit agreement and the HMR event-to-program binding remain open.
The empirical tables do not complete those obligations or prove a numeric error
bound for the point-add circuit.
