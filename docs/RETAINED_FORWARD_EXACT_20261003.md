# Complete exact point circuit with retained forward field arithmetic

Latest integrated result: **2,856,381 Toffolis / 2,197,177 measurements / ≤2,994 static sites**, verified with 727 public audits. See [the complete retained arithmetic record](RETAINED_BOTH_EXACT_20261003.md). The checkpoint below is retained as historical component/integration evidence.

The complete controlled point-addition program is Lean-verified at **3,114,941 static Toffolis**, **2,455,737 measurements**, and **at most 2,994 distinct static logical wire sites** for a finite classical addend. An identity addend still selects the empty program. Static wire support has not been converted into a peak-live qubit measurement.

The same protected `ControlledPointAddSpec.lean` proves the original all-valid-input contract: point addition for both control values, restored control, complete workspace cleanup, and phase restoration for every independent measurement record. Its SHA-256 is `e3d4a181ad1e0e6d4458dc8bcc85d1de7d4ffd6c02c7ce11ee5a11296e08210d`.

## Integrated changes

The routed integer passes use universally proved width bounds across all 512 rounds. Routing saves 130,560 Toffolis over checkpoint `b777104` and adds 1,020 measurements, producing the intermediate full-point result of 3,374,525 Toffolis and 2,714,809 measurements.

The retained forward field endpoint combines exact signed addition, modular normalization and halving. Its threshold cleanup retains and restores the full carry image, reuses the unloaded constant word as comparison workspace, and then erases carries with immediate phase correction. At 256 bits it costs 1,540 Toffolis and 1,541 measurements. Including the existing controlled swap, each cell costs 1,796 Toffolis. The complete division contains all 512 cells, saving 259,584 Toffolis and 259,072 measurements from the routed checkpoint.

The four borrowed padding sites already belong to the shared pool. `FusedSharedRetainedSupport.lean` proves actual gate-support containment through the packed kernel, sign wrapper, cell, replay and division layers. The enclosing full point program retains its original support bound.

| Resource | Routed full point | Retained forward full point |
|---|---:|---:|
| Static Toffolis | 3,374,525 | 3,114,941 |
| Measurements | 2,714,809 | 2,455,737 |
| Static logical site bound | ≤2,994 | ≤2,994 |

The combined saving from `b777104` is 390,144 Toffolis. The saving from the original 7,207,866-Toffoli baseline is 4,092,925, or 56.78%.

## Verification

All Lean ran on the user's CPU pod with pinned Lean 4.28.0 and Mathlib. The warnings-as-errors complete library build passed 3,499 jobs, followed by 674 public axiom queries covering 673 distinct declarations. Every transitive audit used only `propext`, `Classical.choice`, and `Quot.sound`. The existing duplicated query is retained.

The final measured verification took **193 seconds**, consisting of an **87-second incremental full build** and a **106-second axiom audit**. Earlier development compilation, including the 69-second arithmetic-core compilation, is separate from this final verification measurement. No queue delay was introduced for this direct pod run. Local and remote hashes matched for all 387 captured project files before subsequent Markdown-only documentation updates.

Authoritative logs: `/root/ecdsadd-exact/logs/retained-forward-full-point-v1`. The campaign stores the matching source manifest, build log, axiom log, timing record and hash-check record under `skywalk/retained-forward-full-point/`.

## Next exact work

The multiplication stage still uses the previous independent inverse field cell. A retained inverse endpoint requires a separately emitted program and a fresh all-record phase and cleanup proof. Its projected saving is not included in this checkpoint. Measurement-bearing instructions will not be mechanically reversed.

After inverse integration, the next structural screen is an exact in-place dyadic block with joint quotient recovery and deferred orientation. The initial two-cell screen is approximately 944 Toffolis with complete cleanup. Approximate compare windows, clipped carries and sampled convergence schedules remain excluded.
