# Exact history-codec composition

## Scope and baseline

The benchmark work directory is the cloned `ecdsafail-lean` repository.
The manifest is schema version 2, with one `lean` track. Only
`ECDSAAdd/Submission/Entrant` is editable.

The starting source is commit `b1b1f5d90c6f4e7aa7b26c4fc387cf6a22e3b0a4`,
promoted submission `b4462a32-7105-4861-881a-7b5e75e94191`. Its bounds are
2,163,014 Toffolis, 1,502,281 measurements, 1,600 static qubits including
I/O, and 50,000,004 syntax slots. Its Q-times-T bound is 3,460,822,400.
These are published baseline facts, not measurements from this session.

The user explicitly prohibited benchmark execution. No `yukon run`,
`benchmark.sh`, or equivalent scoring execution is part of this experiment.
Lean compilation and axiom inspection remain the intended local validation.

## Research pack

### Schrottenloher, Optimized Point Addition Circuits for Elliptic Curve Discrete Logarithms (2026)

Source: https://arxiv.org/abs/2606.02235, especially section 3.1 and figure 1:
https://arxiv.org/html/2606.02235v1#S3.SS1.

The Euclidean walk stores a compact transcript and replays it against field
registers rather than materializing an inverse and separate products. Groups
of legal branch pairs have fewer states than their binary representation,
so reversible compression releases workspace. This motivates improving the
entrant's `Codec5` implementation without changing the surrounding replay
architecture. The paper's probabilistic comparisons and approximate modular
reductions are not compatible with the challenge's all-input certificate.

### Gidney, Halving the cost of quantum addition (2018)

Source: https://arxiv.org/abs/1709.06648.
DOI: https://doi.org/10.22331/q-2018-06-18-74.

Temporary logical ANDs can be erased with measurement and immediate phase
corrections, reducing arithmetic costs. The protected library and inherited
entrant already use this mechanism extensively. Introducing it into the
codec would require changing its measurement-free reverse-decoder interface,
so it is not used in this bounded composition.

### Luo et al., Quantum Algorithm for Elliptic Curve Discrete Logarithms with Space-Efficient Point Addition (2026)

Source: https://arxiv.org/abs/2607.13816v3.

Register sharing and location-controlled arithmetic offer larger-space
reductions in modular inversion. Adapting that architecture would require
new arithmetic and placement proofs rather than a local circuit replacement.
It is a longer-term direction, not an implemented or measured improvement here.

## Ranked hypotheses

1. **Compose the accepted 12-Toffoli codec with the 1,600-site frontier.**
   Replace the four-Toffoli three-trit pack plus a separate affine-plane
   correction by the accepted pack whose spare codes already contain the
   required affine plane. Keep the same ten ports, holes 5 and 9, and
   `decode = encode.reverse`. There are 816 codec uses per finite addition,
   predicting 816 fewer Toffolis, unchanged qubits and measurements, and
   a Q-times-T bound of 3,459,516,800. Target: the `Codec5` section and
   derived resource statements in `Main.lean`. This is the chosen experiment.
2. **Measure an intermediate codec AND instead of reversing it.**
   Potentially cheaper, but incompatible with the inherited reverse-decoder
   contract without new record-aware correctness and phase proofs. Deferred.
3. **Rebuild inversion with a different register-sharing architecture.**
   Potentially larger improvement, but outside a bounded codec composition.
   Deferred. No asymptotic estimate is claimed as this entrant's score.

Rollback reference: compare `Main.lean` against the starting commit above.
Do not reset or discard unrelated work.

## Exact source reuse

The codec is copied from accepted public submission
`cebe72df-9ef7-45da-a73e-c41d85896ffc`, source commit
`e854d2eb1b15cc76b589acc6b145f4f96d8a8405`.
The emitted `encode` list was compared byte-for-byte with that commit.
It has 178 gate instructions and 12 CCX instructions, with no measurements.
The donor's 1,601-qubit final wrapper is not copied.

The finite-flag hosting, integer-walk repairs, low-half square, selector-free
windows, biased field kernels, and complete outer point-addition proof are
inherited from the immediate 1,600-site base. This experiment does not claim
to have invented those improvements or the donor's SAT-synthesized codec.

Only the codec program, its count/slot statements, and downstream count/slot
literals change. The support, placement, inverse, phase, and point-addition
proof statements keep their interfaces. Codec slots increase from 173 to 178;
the packet bounds are adjusted accordingly without changing the total ceiling.

## ByteAsk consultation

The installed ByteAsk CLI was used in headless, read-only mode with an
eight-turn limit. Its reported model was `gpt-5.4`. The consultation was
restricted to the original codec and final certificate ranges, with explicit
instructions not to edit, build, benchmark, invoke Yukon, or read credentials.
It completed successfully and reported no file changes or executed tests.

ByteAsk suggested searching for pairs of CCX operations whose quadratic
terms cancel after an invertible affine change of their two controls.
It did not identify a concrete qualifying pair or verify a circuit saving.
It also warned that the final compute/use/uncompute trio cannot simply be
deleted. This advice was not used to claim an additional optimization.
The actual code change remains the explicitly credited accepted codec above.

## Checks completed before full compilation

- `git diff --check`: passed.
- Protected source-only policy: passed, 1,565 sources.
- Protected import-layer check: passed.
- Codec list identity against the accepted donor commit: passed.
- No scoring benchmark has been executed.

Full Lean setup, compilation, and transitive axiom inspection remain
necessary before claiming a locally validated certificate. The user
subsequently requested submission without compilation, so those local
checks are skipped and remote validation must decide acceptance.
Immediately before submission, the public frontier had advanced to
3,458,374,400, below this candidate's derived target of 3,459,516,800.
