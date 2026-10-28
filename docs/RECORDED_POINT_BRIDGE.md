# Recorded arithmetic integration

Ordinary `Program` has immediate measurement-controlled Z/CZ correction only.
It has no instruction that reads an earlier classical outcome. A generic
cost-preserving lowering of a deferred correction into that syntax is therefore
not supplied or assumed here. Instead, the point dialogue is composed directly
in `RecordedProgram`; existing ordinary stages are embedded unchanged.

## Closed-module boundary

`RecordedPointArithmeticBackend` has the same arithmetic and clean-boundary
contract as PR #85, but executes with `runWithTape`. It additionally requires
`RecordedWellFormedAt 0`: every referenced outcome belongs to an earlier
measurement within the segment. `RecordedTriple.seq` uses `recordedThen`, which
relocates the second segment's ordinals by the first segment's measurement count.
`at_cursor` proves the same contract at any offset on the caller's global tape.

A forward measurement and its later reverse correction must be assembled into
one closed segment, with their intervening computation, before relocating it.
Do not use `recordedThen` independently on a recovery fragment that refers to
another fragment's records. Within that pair, use the same absolute tape and
cursor; the full pair is relocated together. No outcome is replaced by a newly
sampled measurement. Arbitrary finite/short tapes are covered.

## Workspace decision

The current dialogue pool contains 2,613 scratch wires. A backend may use any
subset and vary internal row widths across steps. A larger declared pool does
not force all those wires into the program's static support. Qubit accounting
must use the union of actually referenced quantum wires, including deferred
correction operands. Classical record ordinals are separate.

No workspace parameterization is needed merely because internal widths vary.
It is needed if the new complete arithmetic requires wires outside this pool,
or if live scratch/phase debt must survive the return boundary. The new local
nine-wire decoder does not establish the full inverse's workspace bound.

## Remaining provider obligation

The bridge does not implement divsteps. The provider must assemble its complete
closed division/multiplication segments and prove the recorded backend contract,
including enabled nonzero input, disabled zero input, arbitrary-record phase
restoration, non-target preservation, actual support, and local-record legality.
The complete quantum layout and full-input stopping bound remain to be proved.
These are concrete missing provider obligations, not a need to redesign the
existing measurement semantics.

## Point composition

`RecordedPointDialog.add_spec` composes the same point-add formula and exceptional
cases directly with recorded arithmetic, preserving control, workspace and phase.
`program_wellFormed` checks the relocated classical references for the complete
program. `program_wires` includes immediate and deferred correction operands.
The finite-constant cost formulas retain the fixed overhead: the two recorded
backend calls plus 109,376 Toffolis and 108,856 measurements.

The bridge is conditional on a backend satisfying its fields. The embedded
ordinary backend provides a concrete witness, not evidence that the new divsteps
provider has already met those obligations. Independent review remains required.

The future submission must explicitly expose a `RecordedProgram` and the
recorded correctness/cost theorems. Existing ValueWalk/Skywalk exports retain
their ordinary `Program` API. This is not a claim of a type-identical ordinary
backend or a compiler from arbitrary recorded programs back to `Program`.
