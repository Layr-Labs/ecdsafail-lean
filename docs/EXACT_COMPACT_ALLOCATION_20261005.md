# Exact compact allocation checkpoint

Verified source: `580d53e0fd420ce802297555be93e48c64221389`.

Both exact Stage 2/5 field wrappers now borrow the restored integer/mask scratch for canonical double/half. Literal seed/unseed replace the materialized 258-bit constant bank. Full-state equivalence bridges preserve the old caller contracts for arbitrary independent measurement records. Every phase/control/workspace restoration obligation remains part of the complete point proof.

| Stage | Static Toffolis | Static measurements | Certified allocation ceiling |
| --- | ---: | ---: | ---: |
| 1. Coordinate differences | 2,046 | 2,046 | ≤1,036 |
| 2. Skywalk-GCD division | 1,185,781 | 857,329 | **≤2,068** |
| 3. Prepare X workspace | 1,023 | 1,023 | ≤1,036 |
| 4. Modular square subtraction | 99,902 | 99,382 | ≤1,297 |
| 5. Forward multiplication | 1,185,782 | 857,330 | **≤2,068** |
| 6. Recover output | 2,301 | 2,301 | ≤1,036 |
| Six-stage subtotal | 2,476,835 | 1,819,411 | ≤2,068 |
| Input/corner classification | 4,104 | 4,104 | ≤1,034 |
| Full controlled finite-addend point addition | **2,480,939** | **1,823,515** | **≤2,068** |

This saves258 allocated logical positions per arithmetic stage and in the full support bound, with unchanged T/M. The certified allocation includes521 resident point/control/classification sites, a1542-site low integer pool, and5 retained guard/repair/selector sites. Exact peak-live width is not separately measured. Allocation support is derived from actual instructions, including all measurement correction branches; no unused ghost mask is counted as an operated qubit.

The literal seed and unseed each cost257 T/257 measurements. Canonical unary double and half still cost511/512 T. Their actual instruction support omits the old bank1798..2055 and auxiliary Cin2313. Untouched virtual sites occur in inherited proof assertions only; the compact support theorem covers every emitted gate.

Remote verification `stage25-compact-point-v1` passed the complete library build (3,704 jobs) in252 seconds and all1,294 public transitive axiom queries (1,293 distinct declarations) in181 seconds:433 seconds total. All599 snapshotted source hashes matched before/after. Original protected point correctness specifications were byte-identical. Allowed axioms are only propext, Classical.choice and Quot.sound. Setup and queue time were each0 seconds; source preparation/transfer were not separately timed.

Authoritative evidence: `/root/ecdsadd-exact/logs/stage25-compact-point-v1`. Local campaign archive: `outputs/lean-stage25-exact-20261004/compact-point-candidate/stage25-compact-point-v1` in the optimization workspace.

The requested ≤1,297 Q and <600,000 T per Stage2/5 remain unfinished. Retained transcript storage and integer/field coexistence require further structural changes. Exact sign-copy release and dyadic blocks are separate unintegrated candidates; no savings from them are included above.
