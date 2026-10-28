# Exact balanced Stage 2/5 checkpoint

Verified source: `33144810a074ad70bf5460961fac6af246d9a814`.

The selected full controlled point-addition circuit uses the independently proved balanced forward and inverse field kernels. Existing public point correctness specifications remain byte-identical. The proof covers the existing valid-input domain, both control branches, arbitrary incoming phase and every measurement record, with clean workspace and restored controls. No sampled correctness or approximate arithmetic is used.

| Point-addition stage | Static Toffolis | Static measurement instructions | Certified logical allocation ceiling |
| --- | ---: | ---: | ---: |
| 1. Coordinate differences | 2,046 | 2,046 | ≤1,036 |
| 2. Skywalk-GCD division | 1,185,781 | 857,329 | ≤2,326 |
| 3. Prepare X workspace | 1,023 | 1,023 | ≤1,036 |
| 4. Modular square subtraction | 99,902 | 99,382 | ≤1,297 |
| 5. Forward multiplication | 1,185,782 | 857,330 | ≤2,326 |
| 6. Recover output | 2,301 | 2,301 | ≤1,036 |
| Six-stage subtotal | 2,476,835 | 1,819,411 | ≤2,326 |
| Input/corner classification | 4,104 | 4,104 | ≤1,034 |
| Full finite-addend controlled point addition | **2,480,939** | **1,823,515** | **≤2,326** |

The ceiling counts a certified allocation including resident point/control/classification sites. It also bounds distinct instruction support. It is not an independently measured exact or minimal peak-live width. Stage order follows the user's diagram; emitted square subtraction and addition of 3x_A commute.

## What changed

Both 512-round replays enter centered representation once and return to canonical representation once. Each selected round emits the proved 1,277-T field kernel, a 256-T routing swap and two selector Toffolis. Each complete replay costs 788,980 T /657,908 measurements, including representation boundaries.

The division field segment includes the original exact entry double and output XOR clear: 789,491 T /658,419 measurements. The independently emitted multiplication segment includes input copy and exact exit half: 789,492 T /658,420 measurements. No measured instruction is reversed.

Both old 257-bit caller interfaces are formally bridged to the new 256-bit centered words. High sites are derived zero from canonical inputs, without an added restriction on the caller's base state. Existing integer trace, zero-divisor repair, control and clean-work contracts remain in the full point proof.

Each stage saves130,572 T and measurements versus `b0a2cf8`; full point addition saves261,144 of each. The baseline reduction is4,726,927 T, or65.58%, from7,207,866.

## Remote verification

All Lean execution ran on the user's CPU pod, project `/root/ecdsadd-exact/ECDSAAdd`.

- Attempt `stage25-balanced-point-v1`: full build passed in568 seconds; audit failed in3 seconds because the aggregate audit module was not built. The diagnostic and source hashes are retained.
- The aggregate audit was added to the normal public root build. No existing query or allowed-axiom rule was removed.
- Attempt `stage25-balanced-point-v2`: complete build passed in30 seconds; all1,249 public transitive axiom queries (1,248 distinct declarations) passed in167 seconds. Total197 seconds.
- All582 snapshotted source hashes matched before and after verification. Original protected public specification files matched their baseline hashes.
- Allowed axioms remain `propext`, `Classical.choice`, `Quot.sound` only. Toolchain setup and queue delay were each0 seconds. Source preparation and transfer time were not separately measured and are excluded.

Authoritative remote evidence is `/root/ecdsadd-exact/logs/stage25-balanced-point-v2`. Local campaign evidence is `outputs/lean-stage25-exact-20261004/balanced-point-candidate/stage25-balanced-point-v2` in the optimization workspace.

## Remaining goal

Stage 2/5 still exceed the requested ≤1,297 Q and <600,000 T. Exact bank-free seed/unseed, their pool support and full-state equivalence to old seed callers are separately verified components; they are not integrated in this checkpoint and no Q saving is credited. Removing the legacy unary carry/constant bank and changing retained-history lifetimes remain necessary allocation work.

A separate512-T cleanup screen requires two full carry banks and exceeds the current776-site kernel ceiling. It is rejected and unselected; neither functional proof nor count compilation is claimed. Its counterexample also rules out collapsing distinct signed carry states as an exact shortcut.
