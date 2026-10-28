# Exact penultimate-swap checkpoint

The complete point-addition source `f83e51c9cd9e1e41dcfcc431f6ef8827e7bb7b57` passed the CPU-pod strict build and all public transitive-axiom checks. This is an integrated verified checkpoint. The original protected point specifications are byte-identical to `6ab64bc`.

| Stage | Logical allocation ceiling | Static Toffolis | Measurement instructions |
| --- | ---: | ---: | ---: |
| 1. Coordinate differences | ≤1,036 | 2,046 | 2,046 |
| 2. Skywalk-GCD division | ≤1,899 | 1,055,040 | 724,550 |
| 3. Prepare X workspace | ≤1,036 | 1,023 | 1,023 |
| 4. Measured streamed square | ≤1,297 | 99,902 | 99,382 |
| 5. Forward multiplication | ≤1,899 | 1,055,040 | 724,550 |
| 6. Recover output | ≤1,036 | 2,301 | 2,301 |
| Six-stage subtotal | ≤1,899 | 2,215,352 | 1,553,852 |
| Input/corner classification | ≤1,034 | 4,104 | 4,104 |
| Complete finite-addend point addition | ≤1,899 | 2,219,456 | 1,557,956 |

The infinity addend emits the empty circuit. The site ceilings include resident point/control sites. They bound logical allocation but are not independently measured exact runtime peaks. The six-stage order is conceptual. The source's square subtraction and subsequent addition of `3x_A` commute in the field.

## Exact change

The already specialized field replay omits terminal cell 511. At the end of cell 510 its two field words coincide. Its entire S-selection window, including 256 controlled swaps and selector cleanup, is therefore the identity. The independent inverse starts with equal words, so its corresponding initial S-window is also removable. The G-window and arithmetic body remain. All 512 integer recording rounds and compressed history restore as before.

Each stage saves 257 T and one measurement. Across the complete point circuit the saving is 514 T and two measurements, with the same 1,899-site support ceiling. This is not a new claim about the minimum qubit schedule or a <600K arithmetic stage.

Forward composition quantifies over arbitrary fresh measurement lists. A proved default-false padding and splicing construction aligns the unchanged prefix and suffix without requiring a minimum list length or correlating independent outcomes. Full-state equality retains phase, controls, history and workspace. Kernel-opaque certified aliases are proof wrappers with proved program equality, not new axioms or emitted gates.

## Verification receipt

Attempt `penultimate-swap-full-point-v1` completed with exit 0. All Lean ran on the authorized CPU pod.

- Build: 763s, all 3,948 jobs passed.
- Audit: 256s, all 1,493 queries passed, covering 1,492 distinct selected declarations.
- Total: 1,019s (16m 59s). Verifier setup and queue: 0s each.
- Sources: 855 hashes matched before and after verification.
- Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx` or new axiom.
- Remote logs: `/root/ecdsadd-exact/logs/penultimate-swap-full-point-v1`.

Source preparation and transfer were not separately timed. The build is the complete strict project build against the pinned toolchain and cached dependency environment. The separate audit checks the selected declarations and their transitive axioms, rather than every declaration in the environment.

Correctness is formal in the original signed-basis/measurement-record semantics. The proof covers all valid input points, controls, exceptional cases and arbitrary incoming phase with clean workspace. No sampling or approximate windows establish these claims. A full quantum-channel semantics bridge remains outside the original model, as described in [proof scope](PROOF_SCOPE.md).

The Stage 2/5 goal remains ≤1,297 peak-live logical qubits and <600,000 static Toffolis if possible. Further progress requires a different fused field arithmetic and history-lifetime interface. Rejected research prototypes do not change this verified resource table.
