# Complete exact point circuit with retained forward and inverse arithmetic

Historical checkpoint/component record. Compact guards are now integrated and fully verified at **2,853,821 Toffolis / 2,194,105 measurements / ≤2,994 static sites**. See [the current integration record](COMPACT_GUARD_EXACT_20261003.md).

The **full controlled point-addition circuit** is Lean-verified at **2,856,381 static Toffolis / 2,197,177 measurements / at most 2,994 distinct static logical wire sites** for a finite classical addend. The identity-addend program remains empty. Static support is a distinct resource from peak-live qubit width, which is still unmeasured.

The protected `ControlledPointAddSpec.lean` is byte-identical to the earlier checkpoints, with SHA-256 `e3d4a181ad1e0e6d4458dc8bcc85d1de7d4ffd6c02c7ce11ee5a11296e08210d`. It covers all valid input points and both control values, restores control and all workspace, and preserves phase for every independent measurement record.

## Integrated inverse arithmetic

The independent inverse endpoint now includes swap undo, exact parity/reduction flag reconstruction, correction subtraction, raw-flag cleanup, signed subtraction, and final canonical halving. All 512 recorded inverse cells are retained. The proof connects the actual transcript to the complete field product and then to the existing controlled point program.

Only Clifford transfer and rotation use the opposite operation order. Every measured subtraction and comparison is a newly emitted forward program with a fresh arbitrary measurement record. No sampled-width, clipped-carry, truncated-comparison or shorter-convergence assumption was introduced.

The packed inverse kernel costs 1,541 Toffolis and 1,541 measurements. With the 256-Toffoli controlled swap, each inverse cell costs 1,797 Toffolis. The multiplication field leg costs 920,576 Toffolis and 789,504 measurements. `FusedSharedInverseSupport.lean` proves actual instruction support within the existing shared pool, so the full point circuit retains its support bound.

| Resource | Previous retained forward checkpoint | Both directions integrated |
|---|---:|---:|
| Static Toffolis | 3,114,941 | **2,856,381** |
| Measurements | 2,455,737 | **2,197,177** |
| Static logical site bound | ≤2,994 | ≤2,994 |

The inverse saves **258,560 Toffolis and measurements**. The combined reduction from `b777104` is 648,704 Toffolis. The reduction from the original 7,207,866-Toffoli source is **4,351,485, or 60.37%**.

## Verification evidence

All Lean ran on the user's CPU pod with pinned Lean 4.28.0 and Mathlib. The complete warnings-as-errors library build passed **3,512 jobs**, followed by **727 public axiom queries covering 726 distinct declarations**. The existing duplicated query remains. Every transitive audit used only `propext`, `Classical.choice`, and `Quot.sound`.

The final measured verification took **193 seconds**, split into **91 seconds incremental full build and 102 seconds axiom audit**. Direct dispatch had no queue delay. Earlier development compilation, including the 68-second arithmetic-core compilation, is recorded separately. All 402 captured project-file hashes matched the CPU pod before the subsequent Markdown-only documentation update.

Authoritative logs: `/root/ecdsadd-exact/logs/retained-both-full-point-v1`. The campaign preserves the matching manifest, build/audit logs, phase timing, runner-start record and hash check under `skywalk/retained-both-full-point/`.

## Remaining exact work

The next structural experiment is an in-place dyadic block with joint two-rail quotient recovery and deferred orientation. The initial two-cell target is approximately 944 Toffolis with complete cleanup. Candidate block savings will remain separate until production integration and complete verification. Peak-live qubit accounting follows once the Toffoli structure stabilizes.
