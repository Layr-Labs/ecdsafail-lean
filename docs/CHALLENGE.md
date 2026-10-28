# Challenge: verified controlled point addition on secp256k1

Tracker: #222. Apache 2.0 (see `LICENSE`, `NOTICE`). Companion to the
[ShorECDLP challenge](https://github.com/VerifiedQC/ShorECDLP/blob/main/docs/CHALLENGE.md).

## Task

Give a circuit family `entry : Point → Program` that, for every public classical point `C`
(including infinity), every control bit `b`, every input point `R` and **every** measurement
record, maps

    control = b, point = R, all other wires = 0
      ↦ control = b, point = (if b then R + C else R), all other wires = 0

and restores the sign. Classical precomputation on the public `C` is allowed.

## Fixed interface (protected, `ECDSAAdd/Challenge/Contract.lean`)

| Wires | Meaning |
|---|---|
| 0 | control |
| 1 | finite flag (infinity = false with zero coordinates) |
| 2–257 | x, little-endian, canonical representative in [0, p) |
| 258–513 | y, little-endian, canonical representative in [0, p) |
| ≥ 514 | must be 0 before and after |

The entrant cannot choose the encoding, the layout, the semantics or the counters.

## What you submit

Edit only `ECDSAAdd/Submission/Entrant/`. In namespace `ECDSAAdd.Entrant` define
`entry : Challenge.Entry`, `bounds : Challenge.Bounds` and
`certificate : Challenge.Certificate entry bounds`. The shipped entrant is the ValueWalk baseline.

`Certificate` requires: correctness (above) for all `C, b, R` and records; physical validity of
every instruction (distinct CX/CCX/CZ wires, both correction lists); and uniform upper bounds,
over every `C`, on Toffoli count, measurements, qubits and total syntax slots.

## Metrics (all recorded)

| Metric | Definition |
|---|---|
| Toffoli | static CCX count, worst case over `C` |
| Measurements | static X-measurements |
| Qubits | distinct wires, I/O ∪ program support (not peak-live, not fault-tolerant qubits) |
| Syntax slots | every instruction, each measurement counted 1 plus **both** correction lists |
| Q × T | qubits × Toffoli, reported by the judge |

Reported numbers are certified uniform **upper bounds**, not exact counts for a particular `C`.

## Scope

Results hold in the repository's signed-basis, fixed-measurement-record model
(`docs/PROOF_SCOPE.md`). They are formal results in this model, not quantum-channel or hardware
claims.

## Baselines (certified through the judge)

| Entry | Toffoli ≤ | Measurements ≤ | Qubits ≤ | Slots ≤ | Q×T ≤ |
|---|---:|---:|---:|---:|---:|
| Skywalk (normalized) | 2,217,386 | 1,557,928 | 1,899 | 47,000,000 | 4,210,816,014 |
| ValueWalk (normalized) | 6,286,806 | 3,779,274 | 3,134 | 61,000,000 | 19,702,850,004 |

"Normalized" rewrites a same-wire CZ as Z and a repeated-control CCX as CX; execution is
unchanged on every record and the Toffoli count can only decrease (see
`docs/BASELINE_NORMALIZATION.md`). Normalization is a proof device; whether a baseline actually
contains such gates is reported by enumeration, not inferred.

## Running the judge

See `docs/CHALLENGE_RUNNER.md`: Python ≥ 3.10, `ECDSA_PAPER_SOURCE` pinned and clean,
editable-boundary check before any cache restore, isolated build, then the trusted Expr-level
judge (`scripts/challenge/judge.lean`) on an overlay containing only Entrant artifacts.

## Organizer limits

Not yet fixed; `Challenge.Within` checks them once chosen.
