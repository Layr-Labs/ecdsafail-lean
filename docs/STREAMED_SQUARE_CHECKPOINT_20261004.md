# Integrated exact streamed Step 4: six-stage resources

Verified experimental checkpoint: `6d3196e`, branch `exact-streamed-square-20261003`.
The full controlled point-addition correctness theorem, including exceptional inputs, disabled control, phase restoration and clean workspace, passes Lean v4.28.0. The strict full build and 749 public transitive-axiom checks passed: 148 s build + 127 s audit = 275 s, zero queue time. A separate 755-query audit also checked the streamed component and its support theorems.

This is an integration checkpoint with a severe Toffoli regression. It is not promoted over the earlier 2,725,817-T production circuit.

| Stage in the six-stage figure | Exact static Toffolis | Q ceiling including resident sites | Measurements |
|---|---:|---:|---:|
| 1. Coordinate differences | 2,046 | ≤1,293 | 2,046 |
| 2. Dialog-GCD division | 1,315,329 | ≤2,579 | 986,367 |
| 3. Prepare X workspace | 1,023 | ≤1,293 | 1,023 |
| 4. Streamed modular square | 1,571,476 | ≤1,297 | 0 |
| 5. Forward multiplication | 1,315,330 | ≤2,579 | 986,368 |
| 6. Recover output | 5,884 | ≤1,550 | 4,604 |
| Six-stage subtotal | 4,211,088 | ≤2,579 | 1,980,408 |
| Input/corner classification outside the six boxes | 4,104 | ≤1,034 | 4,104 |
| Complete controlled finite-addend point addition | 4,215,192 | ≤2,579 | 1,984,512 |

Q values are conservative allocation/support ceilings, not measured exact peak-live results. An execution allocating only the certified support cannot exceed its Q ceiling. Step 4 has a formally proved 1,297-site stage layout including the 521 resident point/control/classification sites and 776 workspace sites. Its exported gate support is 1,289 sites. The earlier 2,865 peak-live figure describes the previous signed-row stage, not this circuit. A final peak-live release-schedule scan is still pending.

The conceptual figure orders preparation of X before the square. Production source executes square subtraction first, followed by adding 3x_A; the two updates commute and use the same resource accounting.

## Why Step 4 is much more expensive

The earlier 82,101-T signed-row square used 81,589 measurements and required 2,865 peak-live sites. The new unitary streamed core uses 287,768 T and 0 measurements: 101,628 T for square producers and cleanup, plus 186,140 T for exact modular folds. It has 708,172 CNOTs. The integration's conservative general control wrapper costs 3 T for each original CCX and 1 T for each original CNOT:

`3 * 287,768 + 708,172 = 1,571,476 T`.

The numerical gate counts come from the Lean-generated exact instruction stream. The formal resource theorem is the exact symbolic expression `863304 + cnotCount(core.program)`, and full-point resource accounting is `2643716 + pointStreamedSquareCost(L)`.

Next work: replace blanket gate control with arithmetic-specific control, eliminate the 126 extra padding sites toward a 1,170-site core-stage target (possibly one extra control scratch), and reduce modular fold overhead. Controlling only folds gives a 1,061,546-T resource screen; it is not yet a verified circuit and is not counted as achieved savings. Approximation knobs remain excluded.

## Source evidence

- `ECDSAAdd/Arithmetic/PointStreamedSquare.lean`: controlled correctness, counts, wire support and 1,297-site bound.
- `ECDSAAdd/Arithmetic/PointDialogSquare.lean`: the active integrated Step 4.
- `ECDSAAdd/Arithmetic/PointDialogCounts.lean`: six-stage and full-point costs.
- `ECDSAAdd/Arithmetic/ControlledPointResources.lean`: full resource theorem with ≤2,579 support.
- `ECDSAAdd/Arithmetic/ControlledPointAddSpec.lean`: original all-input controlled point-addition contract.
- Remote logs: `/root/ecdsadd-exact/logs/exact-streamed-square-v1/full-point-tight-support/`.
