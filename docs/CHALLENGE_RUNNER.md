# Trusted evaluator boundary

This draft certifies controlled secp256k1 point addition in the signed-basis,
fixed-record model. It does not establish quantum-channel correctness or hardware
costs. Classical precomputation on the public addend is permitted.

## Runtime requirement

Python **3.10 or newer** is required, including pinned circuit-source replay.
Set `ECDSA_SOURCE_PYTHON=/absolute/path/to/python3` if the default interpreter is
older. Benchmark, worker verification and development validation check this
selected interpreter before starting work and pass it to source replay. Lean
and Lake must match `lean-toolchain`.

`ECDSA_PAPER_SOURCE` must explicitly name the external circuit-source Git
checkout at `64b5a13aa249f1360846657392e6c66817b26d0f`. No directory default is
used. All three entry scripts verify the directory, exact HEAD and clean tracked/untracked working tree before work;
row-multiplication and lifecycle replay use the same resolver. Set this variable
in the isolated build worker too. The source checkout is an evaluator-managed
external dependency, not entrant input. Source replay additionally checks the
captured generated data against the committed manifests.

## Source boundary

Only `ECDSAAdd/Submission/Entrant/` is editable. Run the evaluator-owned
`check-editable.py` against a pinned trusted Git tree before installing caches.
The filesystem is inspected; candidate Git metadata is not trusted. Imports,
semantics, canonical encoding, full-workspace cleanup and counters are protected.
Organizer numeric thresholds remain undecided; reported numbers are certified
uniform upper bounds, including the infinity addend, not exact scores per addend.
`gateSlots` counts both correction branches; `qubits` includes all 514 I/O wires.

## Build-artifact boundary

`CANDIDATE_BUILDER` is a deployment-owned isolation adapter, not supplied here.
It receives candidate root, trusted root and protected worker verifier as separate
arguments. It must set `ECDSAADD_ROOT`, install trusted caches only after the source
check, prevent writes to trusted storage/controller, terminate every worker process,
and freeze artifacts before returning. Resource/time/network limits are deployment
obligations. This repository does not supply or certify a production sandbox.

The controller copies trusted compiled dependencies into a sealed overlay, then
replaces only Entrant artifacts. Worker-produced Framework/Challenge/Judge artifacts
are ignored. Trusted caches must match `TRUSTED_TREE` and the pinned toolchain.
Independent kernel replay checks entrant declarations. The trusted judge does not
elaborate syntax after importing the entrant: it builds Expr values directly and
uses kernel type equality, an axiom allowlist and kernel reduction for metrics.
Thus imported macros and native `implemented_by` overrides cannot set acceptance
or reported numbers. The runner must keep the trusted judge and toolchain immutable.

Run the protected controller with `CANDIDATE`, `TRUSTED_REPO`, `TRUSTED_TREE`, and
`CANDIDATE_BUILDER` set by the organizer. Missing baseline certificates are rejected;
there is no placeholder or assumed positive example in this draft.
