# X-basis measurement with a retained record

## What is proved

`Framework/RecordedMeasurement.lean` constructs a concrete complex linear
isometry for one X-basis measurement, reset of the measured data bit, and
outcome-dependent Z/CZ corrections. It proves that each output branch has
the bit values and sign phase computed by `measureAndCorrect`.

It also constructs the diagonal isometry for a delayed `phaseFromRecord`
correction, using a bounded index into an existing finite record. This map
preserves every data and record label. Its phase agrees with `runWithTape`.

This is the measured-instruction part of the quantum bridge. It does not yet
prove the bridge for an arbitrary multi-instruction `RecordedProgram`, or
construct a concrete 935-wire point-add instance of `QuantumBudget`.

## Input and output spaces

The input label is `Bits n = Fin n → Bool`.
For target `t : Fin n`, `Cleared n t` is the subtype of labels with bit t false.
There is a proved equivalence:

```
Bits n ≃ Bool × Cleared n t
x ↦ (x t, update x t false)
```

This simply separates the target bit from the other data. It discards no
information. The inverse restores the separated bit.

The quantum map then applies a Hadamard to the Boolean coordinate. That
coordinate becomes the retained measurement outcome m. The other coordinate
is the data with target t reset to zero. The output space is therefore
`EuclideanSpace ℂ (Bool × Cleared n t)`.

The output is a coherent record plus data: a purification of the measurement.
Reading the record produces the ordinary outcome distribution. Discarding
it would require a density-matrix description, which is not supplied here.
The target's fixed-zero state is implicit in `Cleared`; it is not an uncounted
variable. This representation makes no claim of a physical qubit saving.
A resource proof must account for data wires and any coherent record storage.

## The actual linear map

For each reset label z, let a be the amplitude of the input with target false,
and b the amplitude of the input with target true. Before correction:

```
output(false,z) = (a + b) / sqrt(2)
output(true,z)  = (a - b) / sqrt(2)
```

`hadamard_norm` proves norm preservation using the parallelogram law.
`hadamard_twice` proves that this transformation is its own inverse.

The selected correction list then multiplies each output amplitude by +1 or
-1. The sign is computed by the existing `correct` interpreter on z, with
incoming phase false. `phase_norm` proves this diagonal map preserves norm.
Their composition is `measure`, whose norm preservation is `measure_norm`.

The definitions use the interpreter's zero extension outside the finite
register. To interpret a correction list as a circuit wholly within those
n data wires, the caller must additionally establish that all its operands
lie in `Finset.range n`. This patch does not infer a circuit's support or
its live-wire resource bound.

## Exact branch correspondence

For an input basis label x and output record m, the only possible reset data
label is `clear t x`. The branch amplitude is:

```
sign((measureAndCorrect t c0 c1 m <false,extend x>).phase) / sqrt(2)
```

All other reset labels have amplitude zero. `measure_single` proves this
formula. `measurement_basis` proves that the reset data equals the
interpreter output. `measure_signed_single` extends the amplitude formula to
an arbitrary incoming Boolean phase.

This is an amplitude theorem, not merely a statement that the classical
output bits match. The denominator and the sign are part of the proved map.

## Record probabilities are not assumed uniform

`outcomeMass` sums squared output amplitudes over the reset data labels for
a specified record m. `outcomeMass_nonneg` and `outcomeMass_total` show that
these are nonnegative and sum to the input's squared norm. For a normalized
input, they sum to one.

For a basis input, the two X-basis outcomes have equal weight. For a
superposition, contributions interfere before taking squared norms.
`plus_input_norm`, `plus_input_output`, and `plus_input_probability` prove a
normalized plus input with probabilities exactly 1 and 0. Thus a uniform
probability distribution over all interpreter tapes would be incorrect.

## Delayed corrections and composition

`savedCorrection` acts on `Bits n × (Fin k → Bool)`. A `Fin k` index selects an
existing record bit; the type excludes a future or missing record.
`savedPhase_run` and `savedCorrection_single` connect its diagonal sign to
`runWithTape [.phaseFromRecord j cs]` on the corresponding finite tape.
The records are retained and remain available for later operations.

`measure_correction_comp` relates immediate correction to applying the same
correction after a bare measurement when no data operation intervenes.
`followed_by_norm` permits composition with any subsequent linear isometry.
These facts do not automatically establish the semantics of an intervening
arithmetic program or prove a complete recorded-program induction.

## Remaining bridge work

A full recorded-program theorem must still:

1. Use a common data-and-growing-record space for sequential instructions.
2. Preserve prior records when a fresh record is allocated.
3. Prove by induction that every branch corresponds to `runWithTape`, with
   the correct product of normalization factors and accumulated sign.
4. Establish the physical good-subspace agreement needed by `QuantumBudget`
   for the concrete program, including its record/environment outputs.

No numerical failure bound, complete point-add correctness result, or
935-qubit bound follows from this instruction-level patch alone.
