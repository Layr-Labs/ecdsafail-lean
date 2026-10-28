# Replacing point-add arithmetic

The point dialogue can now consume a `PointArithmeticBackend` rather than being
bound to the Skywalk division/multiplication gate lists. This is integration
infrastructure for issue #83, not an implementation of divsteps or a new submission.

## Provider contract

`PointArithmeticBackend.program L false` divides Y by X in place;
`program L true` multiplies Y by X. Inputs X and Y are canonical field values.
The generic control enables the operation. X is required nonzero only when
enabled, including for multiplication because this is a reversible in-place
operation. With the control off, X=0 is permitted and Y is preserved.

For every initial phase and every measurement record list, the provider must
preserve phase and all non-Y wires, and return the stated canonical Y value.
The dialogue pool starts clean and is therefore also restored. Its instructions,
including both measurement correction branches, must stay inside
`L.dialogUsedWires`.

The current contract uses the existing `ControlledPointLayout` and dialogue
pool. Providers needing another workspace must adapt/generalize that layout
explicitly. `RecordedProgram` is not silently embedded: a deferred-measurement
provider must prove its bridge to this ordinary `Program` contract.

## Composition and regression witness

`ParametricPointDialog.add_spec` proves controlled addition for all valid points
and constants, including infinity and exceptional branches, with original work
restored and phase preserved. `finite_frame` preserves all non-point wires.
`program_wires` bounds the actual full program support.

`PointArithmeticBackend.skywalk` satisfies the interface using the existing exact
arithmetic. `skywalk_program` proves equality of the emitted gate list to
`pointCompressedAdd`, so this instantiation changes neither behavior nor cost.
Existing submissions are unchanged.

## Resources

For a finite constant, the actual full program has:

- Toffolis = division Toffolis + multiplication Toffolis + **109,376**.
- Measurements = division measurements + multiplication measurements + **108,856**.

`finite_counts` proves these formulas from the program itself. The ordinary
branch alone adds 105,272 Toffolis and 104,752 measurements. Adding the infinity
constant emits the empty program. `qubits_le` gives a conservative bound by the
static union of declared wires, not a peak-live count or a qubit improvement.
A new provider needs its own tighter support calculation to claim savings.

## Review status

Implementation and self-validation are not review approval. This is the
integration portion (item 7) of issue #83; Dirac must accept the concrete commit
before its checkbox is checked. New divsteps arithmetic, the full termination
certificate and a new submission remain separate unfinished work.
