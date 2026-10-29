# Combined Lean entrant

This entrant combines the promoted 1,890-site circuit (`898d9e8d`) with two
published optimizations: measured Karatsuba sum preparation and cleanup
(`3ad6cb98`), and narrow replay-cell folds (`ee1e7f26`). The implementation and
proofs are collected in `Main.lean`, with sections preserving former module scope.

The narrow segment's instruction-subset theorem transports the stronger
label-2411 avoidance proof, retaining the exclusion of pool sites 1800 and 1804.

| Metric | Verified bound |
|---|---:|
| Toffolis | 2,174,630 |
| Measurements | 1,516,715 |
| Static qubits including I/O | 1,890 |
| All syntax slots | 47,000,000 |
| Q × T | 4,110,050,700 |

The full local benchmark accepted these bounds after a fresh build and kernel replay. The prior promoted base has score 4,110,534,540;
the original Skywalk reference has score 4,210,816,014.

Run from this benchmark work directory:

```sh
LEAN_NUM_THREADS=2 yukon setup --track lean
LEAN_NUM_THREADS=2 yukon run --track lean
```

The certificate covers every valid input point, every addend, both control
values, arbitrary incoming phase and measurement records, and restoration of
all non-I/O work bits. The protected contract and judge are unchanged.
