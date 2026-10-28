# Sequential measured circuits with retained records

`Framework/RecordedQuantum.lean` composes the primitive maps from
`RecordedMeasurement.lean`. The data space is `Bits n`; the record space at a
boundary is `Fin k → Bool`. All records are retained in the coherent output.
This is a purification, not a density-matrix channel with records discarded.

## Representation and physical map

`Circuit n k l` contains proper reversible gate blocks, X measurements,
corrections controlled by an earlier record, and sequential composition.
Every gate and correction operand lies below `n`. Measurement appends its
outcome at index `k`; it does not renumber old records. The measured data
wire is reset to zero, by an isometric inclusion of its cleared subspace.
The tensor lift preserves arbitrary correlations with old records.

`Circuit.program` erases this typing to the existing `RecordedProgram`.
`count`, `wellFormed`, and `support` prove its final cursor, legality of saved
record references, and finite quantum-wire support. `Circuit.semantics` is
an actual complex linear isometry constructed from these primitive maps.
It preserves norm for every input, including superpositions of old records.
`realize` proves every bounded, well-formed recorded stream with proper
ordinary gates has a typed circuit whose erasure is exactly that stream.

## Interpreter-derived amplitudes

`measurement_single` proves the amplitude for a fresh record, preserved old
records, and reset data. Its sign is the phase returned by the existing
`measureAndCorrect` interpreter. Gate amplitudes use the basis action of
`run`; saved corrections use `runWithTape` and the saved finite record list.

`Circuit.kernel` composes these primitive amplitudes by summing over all
intermediate data/record configurations. `kernel_eq` proves by induction on
the complete typed circuit that this kernel equals its actual basis-input
amplitude. `apply_kernel` extends the result to arbitrary input amplitudes.
Multiplication and summation happen before taking absolute squares; no
uniform-outcome assumption is imposed on superpositions.

This module supplies the compositional kernel. The subsequent
`Framework/RecordedPaths.lean` collapses it to one final-tape `runWithTape`
formula and derives a measured quantum budget from `RecordedAgreement`;
see `RECORDED_PATHS.md` for that bridge and its explicit ideal environment.

## Approved error contract

`Circuit.budget_of_kernel` gives `FailureBudget.QuantumBudget` for this fixed
actual map when its kernel agrees on good basis inputs with an independently
specified ideal isometry, and a normalized input law gives bad mass at most
ε < 1. The ideal must include the same output record environment. The
existing `QuantumBudget.error_le` then supplies the vector-error bound.
Kernel equality is still a concrete proof obligation; it is not replaced
by an arbitrary claimed physical realization.

A concrete point-add instance, numerical failure probabilities, and the full peak-live bound
of 935 are not established here. The retained record space also is not a
proof of physical quantum-memory allocation: classical record accounting
and data-wire liveness belong to the resource model.
