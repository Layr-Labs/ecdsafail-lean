# Source-gap composition (task #58)

This increment connects the actual source gaps from PR218 to the producer
interfaces and the original-input failure events. It does not supply the
unproved producer certificates or assert whole-machine phase cancellation.
The source pin, generated programs and layouts are unchanged from PR218.

## Actual lifecycle inputs

`HmrSourceGapInput.lean` proves three caller-facing facts:

- `s2SourceGap_unpark_boundary` derives the complete parked-row boundary from
  the forward certificate and actual K2 execution. The row stays parked;
  the 24 ancillary bits and separate flag bits stay zero; y is demolished.
  The new flags frame is checked against the actual program's mutation targets.
- `s2SourceGap_unpark_input` consumes that boundary through the producer's
  input rule. Only the producer rule and its record predicate remain explicit.
- `s6SourceGap_erase_input` uses the actual K6 full-basis roundtrip to establish
  the inverse input relation. No caller-supplied whole-gap frame is required.

The scratch precondition is supplied by `forward.run`, not by assuming arbitrary
auxiliary inputs are clean. The abstract input rule remains a real producer
obligation. These theorems do not create an actual producer certificate.

## Reached good input and sign output

`HmrSourceSignInput.lean` derives the s2/s6 sign output after `P ++ H`:

1. The original-label good event and reached physical input binding produce
   the forward precondition and `SignGood` via `hmr_pre_of_not_bad`.
2. The forward certificate produces the actual `beforeSign` output value and
   clean ancillary pool on that reached state.
3. The source sign theorem runs at the advanced absolute cursor.

The negate binding is still a separate premise on the actual state after
`P ++ H`. It is not inferred from arithmetic success or reset to the original
input state. Input distribution uniformity is never assumed.

## Exact K6 phase contribution

`HmrSourceGapPhase.lean` checks the actual correction block against 256 Z
corrections: source records `367502+i` control output wires `256+i`.
The records retain absolute ordinals; the source cursor is not subtracted.

`hmrRecordedZList_phase` proves the correction list contributes the XOR of
`record_bit AND current_data_bit`. `s6SourceGap_phaseDelta` proves that the
whole sign / correction / inverse-sign gap has exactly that contribution on
its actual signed intermediate state. The inverse-sign's phase cleanup is
proved using the ancillary bits left clean by sign and unchanged by Z.

`s6SourceGap_after_forward_phaseDelta` obtains clean anc from the forward
certificate. `s6SourceGap_phase_restored_iff` requires that concrete parity to
be false; it does not assert it is false. Cross-segment debt cancellation is
still a separate obligation.

## Source-fixed three-call skeleton

`HmrSourceThreeCall.lean` fixes both actual forward programs, actual K2/K6,
the source unpark program and the actual inverse program. It leaves the
intervening program J explicit. `hmrSourceThreeCall_phase` instantiates the
existing three-call phase theorem using the newly proved input relations.

Both lifecycle preconditions and record predicates use actual intermediate
states and cumulative absolute cursors. No local phase-restoration premise is
introduced. No `WaitingOnProducer` declaration is imported by these modules.

## Remaining work

The producer specifications and input rules, their record conditions, the
negate binding, the actual intervening J and its call precondition, the full
phase-debt cancellation equation, and the endpoint contract must still be
established for the complete source program. All new theorems are conditional
on the listed interfaces and contain no admissions. The separate waiting
module still has 14 obligations. Tasks #58/#59/#60 remain incomplete.
