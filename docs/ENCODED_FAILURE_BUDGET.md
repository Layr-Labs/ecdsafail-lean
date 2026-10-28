# Encoded inverse and division budgets

This is a parameterized application of the measured quantum semantics, not a
compact inverse implementation or a 935-qubit certification.

`Framework/EncodedBudget.lean` takes a finite mathematical input type `X`, an
injective encoding `ι : X ↪ Bits n`, an independently specified mathematical
permutation `e`, and an explicit input law `μ`. The encoding includes every
ancilla and the complete initial state. The output encoding must describe the
complete final state, including restored ancillas.

The physical input law is `μ.push ι`. Its weight at `ι x` is exactly `μ.weight x`,
and its weight outside the encoding is zero. The ideal permutation acts as
`ι x ↦ ι (e x)` and fixes unencoded strings. The exceptional set includes the
encoded bad inputs and every unencoded string. Its physical input mass equals
`μ.mass bad`, so correctness is required only for good encoded inputs.

`budget_of_encoded` applies `RecordedPaths.budget_of_recorded` to this full bit
space. `error_of_encoded` gives the complete-output-vector bound `2 * sqrt ε`
for normalized states whose squared amplitudes match the pushed law. Failed
branches are retained, and no measurement-outcome uniformity is assumed.

## Compact arithmetic application

`Arithmetic/Paper935/FailureAssembly.lean` supplies:

- `inversePerm`: field inversion on secp256k1, with zero mapped to zero.
- `divisionPerm`: `(control, x, y) ↦ (control, x, y / x)` for an enabled,
  nonzero denominator; disabled and zero-denominator inputs are fixed. The
  inverse multiplies by `x`. This agrees with the existing ordinary division
  specification on its nonzero-denominator domain.
- `FailureEvents`: counter overflow, history overflow, deadline/nontermination,
  and integer/coefficient window violations, all on the same original inputs.
- `FailureBounds`: one probability bound per category under the same `μ`.
  `mass_le` uses the existing union bound; overlaps and correlations are allowed.
- `inverse_budget`, `division_budget`, and `error_of_failureBounds`: ready-to-use
  conditional quantum budget/error theorems.

The zero conventions make the mathematical maps total permutations. They do
not establish the physical circuit's behavior at zero. The all-tape correctness
premise must prove that behavior, or the zero inputs must be covered by a named
exceptional event with their actual probability charged to the budget.

## Remaining handoff obligations

1. Supply the actual typed measured circuit (`Circuit n 0 l`). Realization of a
   raw program requires support bounds, proper ordinary gates, and legal record
   references as in `RecordedQuantum.realize`.
2. Supply the concrete injective encoding, including clean workspace, and prove
   all-tape, full-state, phase-preserving `RecordedAgreement` outside the event
   union. There is no axiom, admission, or implementation witness for this proof.
3. Define the events from the actual execution trace; include all occurrences
   across stages and calls, including failure to terminate within the deadline.
   If another failure mode exists, cover it or extend the budget. The correctness
   premise still quantifies over every input outside the declared union.
4. Fix the source distribution and prove each event bound and total `< 1`.
   No uniform denominator distribution is supplied or inferred here. For a
   derived denominator `f x`, `InputLaw.push_mass` identifies its event mass
   with the preimage event under the original law; use this to preserve
   correlations across invocations.
5. Apply the error theorem only after matching the actual state's squared
   amplitudes to the encoded law. Numerical epsilon, full point-add composition,
   and peak-live/gate/measurement counts remain separate obligations.
