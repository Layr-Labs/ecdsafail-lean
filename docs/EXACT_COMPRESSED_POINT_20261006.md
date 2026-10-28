# Exact compressed point-addition checkpoint

Verified full-circuit source: `d6d6b4f8b730faae47ca5720cae9657dcf2bd152`.
The complete selected point-addition circuit passed the CPU-pod strict build and all 1,336 transitive axiom queries, with all 748 source hashes matching before and after verification. This is the promoted full checkpoint.

The protected `ControlledPointAddSpec.lean`, `PointAddSpec.lean`, and `AffineFormula.lean` files are byte-identical to the previous checkpoint. Correctness covers every valid point, both controls, exceptional points, every measurement record, arbitrary incoming phase, and complete work restoration under the original monomial semantics.

| Stage | Logical allocation ceiling, including residents | Toffolis | Measurements |
| --- | ---: | ---: | ---: |
| 1. Coordinate differences | ≤1,036 | 2,046 | 2,046 |
| 2. Skywalk-GCD division | ≤1,899 | 1,059,137 | 728,135 |
| 3. Prepare X workspace | ≤1,036 | 1,023 | 1,023 |
| 4. Measured streamed modular square | ≤1,297 | 99,902 | 99,382 |
| 5. Forward multiplication | ≤1,899 | 1,059,138 | 728,136 |
| 6. Recover output | ≤1,036 | 2,301 | 2,301 |
| Six-stage subtotal | ≤1,899 | 2,223,547 | 1,561,023 |
| Input/corner classification | ≤1,034 | 4,104 | 4,104 |
| Complete finite-addend point addition | ≤1,899 | 2,227,651 | 1,565,127 |

The common support inventory has 521 resident point/control sites and 1,378 pool sites. Its 1,899-site ceiling bounds live allocation but is not an exact measured peak or a globally minimal schedule. Stage 4 is relabeled into the common inventory without increasing its existing 1,297-site ceiling. The infinity addend produces an empty circuit.

The three-symbol history codec and phase-local permutations remove 169 sites relative to the promoted 2,068-site circuit. Each arithmetic stage pays 2,380 additional Toffolis and 340 measurements; the whole circuit pays 4,760 Toffolis and 680 measurements. Both integer directions, all 512 rounds, field replay, seed/unseed and the inactive zero-divisor repair are included.

## Verification evidence

All Lean execution occurred on the CPU pod. Component receipts:

- Physical arithmetic correctness transfer: `mapped-compressed-point-transfer-v4`, 397 seconds.
- Concrete arithmetic binding: `mapped-compressed-point-arithmetic-v1`, 6 seconds.
- Generic point composition: `compressed-point-dialog-steps-v1`, 8 seconds.
- Complete point correctness: `compressed-point-dialog-spec-v3`, 45 seconds.
- Complete point counts and support: `compressed-point-dialog-resources-v1`, 8 seconds.

These component times include inline axiom queries; separate audit timing is not available for these attempts. Their public proofs use only `propext`, `Classical.choice`, and `Quot.sound`. Failed infinity-branch proof attempts are retained in the evidence ledger and are not credited.

Full verification attempt: `compressed-full-point-v1`, exit 0. Build: 967s for 3,863 jobs. Audit: 194s for 1,336 queries (1,335 distinct declarations). One second between phases gives 1,162s wall time (19m 22s). All 748 hashed source/configuration/script files matched before and after verification. Verifier setup and queue were each zero seconds; source preparation and transfer were not separately timed. Only standard axioms were present.

## Remaining Stage 2/5 targets

The requested ≤1,297 Q and <600K T per stage remain open. Retaining the full 854-site compressed history alone exceeds the available 776-site workspace budget. Copying the incumbent's early field-cell ordering with our current two simultaneous 256-bit carry banks also needs 1,549 sites before history and extra scalars. That is a limitation of this representation and ordering, not a global lower bound.

The next exact candidate must reduce field carry overlap and interleave field/history lifetimes together. A screened 16-bit carry-capped native adder increases the arithmetic-stage Toffoli cost and does not reduce the field-dominated whole support; it is rejected for this target.
