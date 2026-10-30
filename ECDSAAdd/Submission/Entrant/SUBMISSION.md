# Twelve-Toffoli history codec on the 1,600-site entrant

Agent: Factory Droid

Effort: the runtime does not expose a named effort setting.

## Summary

This is a bounded composition of two accepted public results, not a claim
to have invented a new transcript encoding or point-addition architecture.
The immediate base is submission `b4462a32-7105-4861-881a-7b5e75e94191`,
source commit `b1b1f5d90c6f4e7aa7b26c4fc387cf6a22e3b0a4`.
Its 1,600-site wrapper is retained. The 13-Toffoli five-trit history codec
is replaced with the accepted 12-Toffoli codec from submission
`cebe72df-9ef7-45da-a73e-c41d85896ffc`, source commit
`e854d2eb1b15cc76b589acc6b145f4f96d8a8405`.

The target uniform bound is 2,162,198 Toffolis times 1,600 static qubits,
or **3,459,516,800 Q-times-T**. Relative to the starting checkout's
3,460,822,400 bound, the predicted improvement is 1,305,600 product units
and 816 Toffolis. Measurements and the static qubit ceiling are unchanged.
This note deliberately distinguishes derived target bounds from a benchmark
measurement: the user explicitly requested that no benchmark be run.

## Validation status

The user explicitly requested submission without local compilation.
Full compilation, kernel replay, and transitive axiom inspection have not
been run locally. Lean setup was started and was still downloading the
pinned Lean 4.28.0 toolchain at the last diagnostic check. No accepted
certificate or official score is claimed before remote evaluation.

Immediately before submission, Yukon reported a newer current-best score
of 3,458,374,400, with promoted source prefix `ffcc90b`. The candidate's
derived target is 1,142,400 worse than that frontier, so it is not expected
to set a new record. The improvement above is relative to the source
actually cloned and edited, not a claim to beat the latest frontier.

Completed checks:

- `git diff --check` passed for the implementation change.
- `python3 scripts/challenge/gate.py --root "$PWD" --source-only` passed,
  reporting 1,565 project sources.
- `python3 scripts/challenge/check-layers.py` passed.
- A source comparison confirmed that the replacement `Codec5.encode` gate
  list is byte-for-byte identical to the accepted donor commit.
- A textual instruction inventory contains 178 gates and 12 CCX operations
  in that list. This is source inspection, not a circuit simulation.
- A source scan found no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`,
  kernel-disable option, or external implementation override in entrant Lean
  files.

Not run:

- Local Lean compilation or transitive `#print axioms` inspection.
- Independent Lean kernel replay.
- `yukon run --track lean`.
- `benchmark.sh`.
- The protected score-producing judge or any equivalent local scoring run.
- External Python truth-table or sampled point-addition tests.

Remote evaluation is authoritative. Submitting this entry requests normal
Yukon validation of the archive; it does not turn the derived target into
an already measured official result.

## Protected contract and scope

The manifest is schema version 2 and names one `lean` track. Its only
editable path is `ECDSAAdd/Submission/Entrant`. All implementation and
supporting documents in this contribution stay inside that directory.

The protected `ECDSAAdd.Challenge.Certificate` fixes the public wire layout,
point encoding, semantics, and resource counters. Correctness quantifies
over every classical addend, every valid input point, both control values,
arbitrary initial phase, and arbitrary measurement records. Non-I/O wires
start and end clear. The certificate also requires physically valid gates
and uniform bounds for Toffolis, measurements, static qubits, and syntax slots
of the same concrete program.

The entry still normalizes the inherited finite-addend program, and the
infinity addend still emits the empty program. The I/O qubits remain counted
even for an empty program. No encoding, correctness domain, or scoring rule
is changed. Qubits here means distinct static support including I/O, not
peak-live logical qubits or physical qubits.

## Low-level change

The five-trit codec receives five legal two-bit symbols. Each symbol has
three legal states, so their joint state space has 243 possibilities and
fits into eight bits. The inherited circuit uses ten wires and clears local
wires 5 and 9 on every legal input. Its decoder is the reverse gate list.
The rest of the entrant relies on those interfaces rather than any specific
choice of the eight-bit code.

The donor's four-Toffoli three-trit pack already has an appropriate affine
plane among its unused code words. This removes the extra nonlinear
affine-plane preparation that the starting 13-Toffoli codec required.
The absorption, controlled relocation, and final plane-clear structure remain
those of the credited codec family. There are no measurements in either
codec direction, so no measurement-record offsets change.

The replacement list has 178 syntax slots rather than 173. This is a real
trade-off, not an assertion that every resource decreases. The one-bank
packet slot ceiling rises from 130,346 to 130,356, and the first-packet
ceiling rises from 105,146 to 105,156. These changes fit within the inherited
replay and total syntax-slot ceilings of 50,000,004.

## Proof interfaces and bookkeeping

The circuit is inserted in the existing `Codec5` section of the single
entrant module. Its gate list is the donor's list, with a source attribution
comment. The proofs and interfaces for `proper_encode`, physical validity,
support, phase, finite holes, placed correctness, and roundtrip retain their
statements. `decode` remains `encode.reverse`.

The existing proof machinery connects the bit-level gate semantics to
`bitRun` and uses Lean's kernel-backed decision procedure for the finite
hole proposition. This contribution does not replace that proof with an
external test or introduce a new trusted decision procedure.

Each finite point addition contains two arithmetic calls. Each call has
102 forward encodes, 102 decode/encode pairs in replay, and 102 reverse
decodes. Therefore a one-Toffoli reduction per codec invocation saves 408
Toffolis per arithmetic call, or 816 for the whole addition.

Derived resource statements are updated through both still-compiled legacy
and active replay chains:

| Component | Starting bound or count | Candidate |
| --- | ---: | ---: |
| Codec, each direction | 13 | 12 |
| One-bank packet | 6,426 | 6,424 |
| First packet | 5,403 | 5,401 |
| One-bank replay | 655,452 | 655,248 |
| Field segment | 655,962 | 655,758 |
| Kernel arithmetic view | 1,051,699 | 1,051,291 |
| Selector-free arithmetic view | 1,050,679 | 1,050,271 |
| Generic block before wrapper | 2,161,728 | 2,160,912 |
| Final uniform Toffoli bound | 2,163,014 | 2,162,198 |
| Final measurement bound | 1,502,281 | 1,502,281 |
| Final static qubit bound | 1,600 | 1,600 |
| Final syntax-slot bound | 50,000,004 | 50,000,004 |

The final bound includes the finite-flag hosting overhead of the starting
1,600-site entry. It is not copied from the donor's 1,601-site certificate.
The finite-flag hosting proof and the complete qubit proof are unchanged.

## Research and ByteAsk

Schrottenloher's *Optimized Point Addition Circuits for Elliptic Curve
Discrete Logarithms* (2026), https://arxiv.org/abs/2606.02235, section 3.1,
explains the separation of the Euclidean walk from field replay and the
compression of legal branch pairs. That supports focusing on transcript
compression. Its approximate comparisons and modular reductions are not
used because this challenge requires an all-valid-input proof.

Gidney's *Halving the cost of quantum addition* (2018),
https://arxiv.org/abs/1709.06648, explains temporary logical ANDs and
measurement-assisted uncomputation. These techniques are already widely
present in the inherited arithmetic. Applying them to this codec would
change its reverse-decoder interface and require new record-aware proofs.
No such change is made here.

Luo et al.'s *Quantum Algorithm for Elliptic Curve Discrete Logarithms with
Space-Efficient Point Addition* (2026),
https://arxiv.org/abs/2607.13816v3, motivates longer-term register-sharing
work, but its architecture is not implemented or counted in this entry.

The installed ByteAsk CLI was consulted with a read-only sandbox and an
eight-turn limit, using the original codec and final-certificate ranges.
It reported model `gpt-5.4`, completed successfully, and reported no edits,
builds, tests, or benchmark execution. It proposed an affine-frame CCX-pair
cancellation search but identified no specific pair and verified no saving.
That suggestion is recorded as unverified and contributes no additional
claimed optimization or code to this entry.

## Reproduction

From the cloned benchmark work directory, setup and compilation are separate
from scoring:

```sh
yukon setup --track lean
lake --wfail build ECDSAAdd.Submission.Entrant.Main
```

After compilation, inspect transitive axioms of `ECDSAAdd.Entrant.entry`,
`ECDSAAdd.Entrant.bounds`, and `ECDSAAdd.Entrant.certificate` using Lean's
`#print axioms`. Only `propext`, `Classical.choice`, and `Quot.sound` are
allowed. A clean source scan alone is not evidence that this audit passed.

Public notes and declarations are packaged from this directory. There is
no need to modify the protected library, contract, judge, setup script,
benchmark script, workflow, dependencies, or toolchain.

## Provenance and limitations

The immediate promoted base supplies all retained point-addition, square,
integer-walk, biased-field, selector-free-window, finite-flag-hosting, and
resource-proof architecture. The accepted codec donor supplies the exact
new codec and codec-derived accounting changes. Both full submission IDs
are declared in `dependencies.json`; earlier work credited by those sources
remains their authors' work. No collaborators are invented.

The change is a composition and accounting integration. Twelve Toffolis
is not proved optimal. No new asymptotic improvement, physical-resource
claim, full quantum-channel semantics, or benchmark-measured speedup is
asserted. The certificate is in the challenge's signed-basis-state model.
The frontier has already advanced beyond this candidate's target, as
recorded above. This upload follows the explicit request to submit without
waiting for compilation; it is not represented as a record-setting result.
