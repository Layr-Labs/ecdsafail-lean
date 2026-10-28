# Baseline syntax-slot bounds

The ValueWalk reference entrant has a complete certificate for every public
addend, including infinity. Its declared bounds are:

| Metric | Uniform upper bound |
| --- | ---: |
| Toffoli instructions | 6,286,806 |
| Measurements | 3,779,274 |
| Distinct wires, including fixed I/O | 3,134 |
| Total syntax slots | 61,000,000 |

Total syntax slots include each measurement and both correction lists, even the
branch not taken. Normalization preserves this count. These are upper bounds,
not claims of exact cost on every addend. The observed C=G count of 49,425,562 is
only a comparison point and is not used in any proof.

The slot proof composes bounds for constant masks, carry computation and erasure,
comparison, modular operations, width-narrowed value walks, replay loops,
Karatsuba squaring, reduction, classification, and corner handling. It does not
expand the complete circuit, raise reduction limits, or assume successful input.
The reusable lemmas are in `ECDSAAdd/Baselines/Slot*.lean`; the whole-program
bound and certificate are `normalizedValueWalk_gateSlots_le` and
`valueWalkCertificate`.

`scripts/challenge/validate.sh` builds the real entrant and runs
`valuewalk_acceptance.py`. That test independently replays the entrant's compiled
module, invokes the protected kernel-based judge, and checks all reported bounds.
The protected controller still requires a deployment-supplied isolated builder;
local acceptance is not a production sandbox certification.

Skywalk also has a complete certificate for every public addend, including
infinity. Its uniform bounds are:

| Metric | Uniform upper bound |
| --- | ---: |
| Toffoli instructions | 2,217,386 |
| Measurements | 1,557,928 |
| Distinct wires, including fixed I/O | 1,899 |
| Total syntax slots | 47,000,000 |

The slot bound composes the native first step, 511 compressed integer steps in
each direction, history codecs, selected field replay, measured squaring,
recovery, classification, and corner handling. It includes both correction
lists for every measurement. In particular, the field segment is bounded by
14,100,000 slots, each wrapped arithmetic call by 20,600,000, and measured
squaring by 5,000,000. The whole-program theorem is
`normalizedSkywalk_gateSlots_le`; `skywalkCertificate` also consumes the
independently proved physical-gate legality theorem.

These are conservative syntax-slot bounds, not exact scores or peak-live-wire
bounds. They do not establish a 935-qubit circuit. The default reference Entrant
remains ValueWalk; the Skywalk certificate can be selected instead without
changing the protected contract.

`skywalk_acceptance.py` compiles the Skywalk certificate as an alternative Entrant
in an organizer-created temporary overlay. It independently replays that module
and requires the unchanged protected judge to accept all four declared bounds.
The default ValueWalk Entrant is not modified by this regression.
