# Source-shaped three-call agreement

Tracker: #213. Task #59 remains open.

`HmrSourceAgreement.lean` derives `RecordedAgreement` from the actual-source
phase composition in PR219. It does not assume `RecordedAgreement` as an input.
The fixed source call programs are s2 forward/unpark and s6 forward/inverse;
the intervening program `J` is an explicit parameter.

## Required evidence

`HmrSourceRunConditions` contains the two legal-cursor facts, the s2 input
precondition, the s6 precondition on the actual output of s2 plus J, and the
two producer record relations. The cumulative cursor is preserved. The
producer specifications and input rules are explicit parameters.

`hmrSource_run_eq` additionally requires:

- Equality of the complete final basis state with the independently specified
  output encoding, including auxiliary wires.
- Cancellation of the total `hmrThreeCallDebt`. This is one equation for the
  whole chain; it does not require separate phase preservation of every stage.

The theorem obtains the phase formula from `hmrSourceThreeCall_phase` and then
combines phase and basis equality. No new admissions are introduced.

`hmrSource_recordedAgreement` requires this evidence for every original input
outside the declared bad event, every initial phase, and every measurement
tape. It does not reset the s6 state/cursor or assume a distribution of tapes.
The bad event must be specified independently of successful execution.

## Conditional quantum error

`hmrSource_empirical_error` uses the same nine-cell bad set and original input
law as `EmpiricalBudget`. It requires `c.program = hmrSourceThreeCall J`, so an
unrelated legal quantum circuit cannot stand in for the source-shaped program.
The independent ideal permutation, encoding, normalized amplitude vector,
matching pushed-forward input law, assumed population bounds, and total < 1
remain explicit. The conclusion is the existing symbolic 2 sqrt(total) bound.

Sample frequencies do not discharge the population inequalities. The two
assumptions and empirical evidence remain described in `ASSUMPTIONS_B5.md`.
The selected input law is the point-addition-denominator-induced law; the
interface remains polymorphic so it does not silently assert uniformity.

## Remaining integration

This file constructs neither the actual producer certificates nor their
record facts. It does not identify J, prove full output encoding, or solve the
total phase cancellation equation. It also does not construct the typed Circuit
or certify any point-addition prefix/suffix surrounding this chain. Such
surrounding operations must be included and proved before claiming complete
point-addition error. The new bridge is conditional, not a completed task #59,
and says nothing about the whole-machine 935 peak.
