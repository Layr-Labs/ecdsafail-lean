# Verified exact direct-divisor checkpoint

The full controlled point-addition source `b0a2cf8be741b3a8028161f16f9da2bc5208e659` passed the remote pinned Lean build and all1,113 public axiom queries. All514 manifest source hashes match before and after checking, and the original protected point-correctness specifications remain byte-identical. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

Full resources: **2,742,083 static Toffolis /2,084,659 static measurement instructions /≤2,326 logical sites**. These sites give an allocation and peak-live ceiling; the exact live peak is unmeasured. No sampling or approximation establishes the correctness proof.

| Stage | Static T | Static measurements | Certified allocation ceiling |
|---|---:|---:|---:|
|1. Coordinate differences|2,046|2,046|≤1,036|
|2. Division|1,316,353|987,901|≤2,326|
|3. Prepare X|1,023|1,023|≤1,036|
|4. Specialized square|99,902|99,382|≤1,297|
|5. Multiplication|1,316,354|987,902|≤2,326|
|6. Recover output|2,301|2,301|≤1,036|
|Corner classification|4,104|4,104|≤1,034|
|Full finite-addend point addition|2,742,083|2,084,659|≤2,326|

The original X word is repaired from zero to one using a retained flag, then used directly by the integer GCD. Two field selectors choose the actual transcript when enabled and the exact divisor-one transcript otherwise. The integer walk restores X, the zero repair is undone, and all selectors and scratch return to zero with unchanged phase for every measurement record.

Compared with the previous `9ea2e58` checkpoint, the full allocation ceiling falls253 sites and Toffolis increase2,048 (1,024 per arithmetic stage). The previous lower-T/higher-Q result remains a separate verified option. The static-ceiling Q×T proxy falls from7,066,550,265 to6,378,085,058, about9.74%; this is not a measured incumbent-compatible score.

Verification attempts are preserved under `/root/ecdsadd-exact/logs/stage25-direct-point-v1` and `v2`. Attempt1:346s successful full build,178s failed expanded audit because three preserved legacy entry points were no longer imported. Attempt2 restored their import and diagnostic output, retaining all checks:10s cached full build +149s successful full audit =159s. No new toolchain setup or verifier queue delay; source preparation/transfer is separate and not included. The cached timing is not a fresh clean-build time.

The Stage2/5 targets≤1,297Q and<600KT remain unmet. A cheaper balanced field forward/inverse prototype emits1,277/1,276T and1,275/1,276 measurements with776 standalone touched sites. Reduced-width arithmetic, phase and cleanup diagnostics pass; its Lean circuit proof, representation conversion and full integration remain outstanding. The776-site figure does not include complete-stage integer/history/resident storage.
