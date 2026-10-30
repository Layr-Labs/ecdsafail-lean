# Biased single-bank arithmetic with the faster square stack

The candidate combines the biased-kernel entrant `013bbada` with the
one-bank-compatible square stack from `a3bc77be`. It retains the shared affine
input classifier and the 1,637-site support certificate.

| Metric | Verified bound |
|---|---:|
| Toffolis | 2,169,697 |
| Measurements | 1,510,255 |
| Static qubits including I/O | 1,637 |
| All syntax slots | 45,600,000 |
| Q × T | 3,551,793,989 |

The full protected benchmark passed, including compilation with warnings as errors, independent kernel replay, allowed-axiom checks and expression-level scoring. The biased-kernel base scores 3,570,722,620 Q×T.
The original Skywalk reference scores 4,210,816,014 Q×T.

The square ends in ordinary orientation, so its following correction is
`fastConstAdd 3*cx`. Its extra scratch is borrowed from existing zero pool sites
and is included in the support proof. Main.lean contains the complete circuit
and certificate in sections preserving the source modules' scope.

Run from the benchmark work directory:

```sh
LEAN_NUM_THREADS=2 yukon setup --track lean
LEAN_NUM_THREADS=1 yukon run --track lean
```

The protected contract, semantics, resource counters and judge are unchanged.
The certificate covers all valid input points and addends, both controls,
arbitrary phase and measurement records, and complete non-I/O work cleanup.

The register-list uniqueness proof uses structural range disjointness, and the endpoint slot bound is proved through a generic layout lemma. These avoid expensive concrete evaluation during kernel replay.
