# Actual row multiplication program data

`HmrRowMulSourcePrograms.lean` defines the three actual calls emitted by
`circuit.py` at source commit `64b5a13aa249f1360846657392e6c66817b26d0f`:

| Call | Lean program | Original operations | HMR | Borrow/release pairs | Temporary wire |
|---|---|---:|---:|---:|---:|
| H2 | `s2ForwardProgram` | 2,185,556 | 197,474 | 498 | 804 |
| H6 | `s6ForwardProgram` | 2,185,556 | 197,474 | 498 | 856 |
| R6 | `s6EraseProgram` | 2,203,069 | 197,474 | 498 | 856 |

These are data definitions, with no execution theorem or assumption producing
programs. This delivery does not establish `HmrRowMulSpec`, support, readiness,
clean release, phase correctness, the complete point-add program, or its peak
resource bound. The original operation totals include SWAP and R and are not
Lean instruction counts. The manifest reports both totals separately.

## Source and representation

All line numbers below refer to the pinned source tree:

- `tasks/modinv-point-add/circuits/divsteps/engine.py:3254–3299` emits the
  forward/inverse `row_mul` schedule, with 256 scan positions and 242 additional
  halvings. The first scan position uses the copy fan; the other 255 use CMA.
- `engine.py:3301–3330` implements lift and row reduction; the inverse call
  borrows the output word for its inverse fold.
- `engine.py:3200–3246` allocates a temporary in each fold stage, emits the
  arithmetic, and recycles it. `engine.py:2284` delegates CMA to
  `tasks/modinv-point-add/circuits/_shared/luo_core.py:1341`.
- `uncompute/builder.py:1620–1655` emits R on recycle. R is allocation lifecycle
  information in this export, **not** a reset instruction in Lean.

The exporter executes the original `build_circuit`, observes all earlier
measurements, and captures every original operation of each target call. Each
of the 756 template occurrences is compared in full against its canonical
operand/measurement stream; a differing occurrence is rejected. Nine templates
contain 24,354 original operations in total. Each Lean template is divided into
private lists of at most 96 instructions. Public programs concatenate actual
ordered uses with their physical operands. The inverse stream is captured from
the source's inverse call, not obtained by reversing measured instructions.

Canonical ports are sign (0), row (1–280), multiplier (281–536), output
(537–792), 24 ancillas (793–816), flag (817), temporary (818), and the current
scan control (819). The capture checks all fixed ports are distinct and every
quantum operand is mapped. The control varies with the scan occurrence.

SWAP expands using the existing `swapBits` order: CX(b,a), CX(a,b), CX(b,a). HMR becomes `measureX`; consecutive conditional
Z/CZ corrections referring to that HMR are its immediate corrections. Other
corrections use their actual absolute measurement ordinal. The call starts are
53,734, 422,703, and 620,345. Classical outcome reuse is resolved to ordinals
while observing the original stream.

R contributes no quantum instruction. The `*Lifecycle` tables record each
borrow and release with its original-operation boundary, normalized-program
boundary, relative measurement position, and physical wire. Each call contains
498 pairs. `RowMulReleaseZero events stateAt` explicitly requires the wire to
be zero at each release boundary; it is an obligation, not a proof or a reset.
The state supplied to this obligation must later be tied to actual execution.
This table does not by itself prove arena ownership or allocation validity.

## Reproduction and validation

Use Python 3.10 or newer and a clean checkout of the exact source commit:

```sh
ECDSA_PAPER_SOURCE=/path/to/uncompute-paper \
  python3 scripts/paper935/generate_row_mul.py --check
ECDSA_SOURCE_PYTHON=python3 ECDSA_PAPER_SOURCE=/path/to/uncompute-paper \
  bash scripts/verify.sh
```

The default source location is a sibling `uncompute-paper` directory. CI checks
out the same pinned source into `.source-uncompute` and sets the source path. The
checker replays **all 6,574,181 original operations**, checks every occurrence,
then compares all generated Lean files and the manifest byte for byte. It does
not just compare summary counts. The manifest also records source-file hashes,
the full occurrence schedule, and physical raw-stream hashes. Source replay is
an external data-transcription check; Lean checks the resulting definitions.
All 29 new public data declarations and six normalization/comparison lemmas are included in the strict existing axiom
audit. This change adds no waiting proof, `sorry`, or axiom.

Local full validation passed 4,569 build jobs and 3,908 exact public-entry audits
in 321.94 seconds, including full source replay. The 3,873 baseline entries are
unchanged; 29 data declarations and six lemmas are appended.

## Normalization proof follow-up

`HmrSourceNormalization.lean` proves the selected three-CX lowering exchanges
bits and preserves phase, and that both conventional expansions agree. It also
proves immediate measurement/correction fusion on arbitrary tapes (including
short tapes). The manifest names these rules and their Lean lemmas.

Source CCX operand order and neighboring CX order are retained. Separate
symmetry/commutation lemmas support comparison against older presentations;
they do not rewrite the generated stream. The old fold list has reversed CCX
controls and some exchanged adjacent same-target CX pairs. Therefore producer
contracts must use full-state semantic prefix equivalence, not assume literal
list equality. The complete source-prefix equivalence is a later obligation.
