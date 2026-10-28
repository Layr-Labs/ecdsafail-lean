# From recorded execution to a measured quantum budget

`Framework/RecordedPaths.lean` completes the interpreter bridge for bounded,
well-formed programs represented by `RecordedQuantum.Circuit`.

## Final-record formula

`Circuit.kernel_final` collapses the intermediate-state sums. For a fixed
input basis label and final record, the only possible data output is the
basis returned by `runWithTape`. Its amplitude is the interpreter's sign
phase multiplied by `(1 / sqrt 2)^M`, where M is the number of measurements.
Old record labels must equal the corresponding prefix of the final record.

This is an amplitude statement for a single basis input. For superposed
inputs, amplitudes add first. Record probabilities can interfere and are
not assumed uniform. `recordMass_nonneg` and `recordMass_total` give the
Born marginal and its total mass for the actual full program.

`Circuit.semantics_eq_of_program_eq` shows that regrouping or retyping the
same erased program does not change its physical linear map. The map is
fixed by execution, not selected as an arbitrary correctness witness.

## Independent ideal and error bound

Programs in `budget_of_recorded` start with no prior records. `actual`
initializes the unique empty record and executes the concrete isometry.
`ideal l e` applies a separately supplied mathematical basis permutation e
and tensors it with an independent normalized uniform state on l retained
record bits. `uniform_norm` proves this ideal environment has norm one;
it is not a hypothesis about the actual measurement outcomes.

`basis_of_recorded` proves that the existing all-tape `RecordedAgreement`
implies equality of the actual and ideal purified basis outputs outside
the designated bad input set. In particular, agreement includes the
interpreter phase, so unresolved relative signs cannot be ignored.
`budget_of_recorded` then produces the adopted `QuantumBudget` from that
classical proof, the normalized input law, and the bad-mass bound ε < 1.
Its `error_le` theorem gives vector error at most 2√ε for normalized input
states whose amplitude law matches that input law.

The ideal permutation must be fixed by the intended mathematical
operation. It cannot be chosen after the fact to copy an incorrect actual
operation. Clean-input and ancilla conditions must be accounted for in
the input law and good-input proof. The theorem does not supply them.

## Scope

`RecordedQuantum.realize` covers every bounded well-formed stream whose
ordinary reversible gates have distinct controls and targets. The result
can be used with the theorems here through its exact program erasure.
Measurements and delayed corrections retain their existing interpreter
semantics. The old exact Triple and RecordedTriple interfaces are intact.

These theorems describe a coherent purification retaining all measurement
records. They do not assert a diamond-distance bound or a result about
records after discarding the environment. The retained mathematical
record space is not a physical live-wire allocation certificate.

The actual compact point-add implementation still needs its own
RecordedAgreement proof, independently specified ideal operation, input
law and numerical failure bound, and complete peak-live bound of 935.
None of those circuit-specific obligations is discharged by this bridge.
