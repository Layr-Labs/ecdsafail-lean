# Exact zero-seeded comparator checkpoint

Verified source: `092e87c42b22197769202f203c78b2ec93b24861`.

| Scope | Static Toffolis | MX instructions | Certified support/allocation ceiling |
|---|---:|---:|---:|
| Stage 2 division | 1,054,002 | 724,536 | ≤1,899 |
| Stage 5 multiplication | 1,054,512 | 724,536 | ≤1,899 |
| Full controlled finite-addend point addition | 2,217,890 | 1,557,928 | ≤1,899 |

Compared with `82a69cb`, this saves 2 T and 2 MX per arithmetic stage, 4 T and 4 MX overall. Q is unchanged. Exact runtime peak-live Q is not separately measured. The larger ≤1,297 Q and <600K T per-stage targets remain open.

The literal comparison to one starts with carry-in zero. Its first borrow is NOT(input bit), so an X/CX pair computes it and a CX/X pair clears it. The new component proves full-state equivalence, independent record equivalence, counts and support subset. Enter and fresh Leave use the actual existing carry/frame premises. Later record slices use the new measurementCount; no sample or shared ordinal assumption replaces the all-record contract. The original generic comparator and three protected specification files are byte-identical to the prior checkpoint.

Full source-bound verification completed at 2026-10-07 06:22:38 UTC. The successful retry took 39 seconds cached build and 240 seconds transitive audit, 279 seconds total. It passed 3,983 build jobs and 1,596 queries covering 1,595 distinct public declarations. All dependencies use only propext, Classical.choice and Quot.sound. Source checks matched 886 Lean files and four verifier/build metadata files before and after. Setup and queue time were zero; source preparation and transfers are excluded.

The first full attempt at `a419ebf` failed after 1,666 seconds, before audit, because PointDialogCounts still stated the older legacy totals. Only those four numerals were corrected for the successful retry. Its earlier completed build work was reused. Report this failed time separately from the successful cached retry.

Independent Axtro Trio reviews cover the component, actual caller patch, legacy repair and final source/axiom receipt. Authoritative pod logs: `/root/ecdsadd-exact/logs/zero-head-full-point-v2`. Local campaign receipts: `outputs/lean-stage25-exact-20261004/axtro-trio-20261007/builder/verification/zero-head-full-point-v2`.

This is complete formal point-circuit verification in the project's original monomial basis/phase model. It is not sampled-input correctness evidence. The signed cofactor digit experiment remains an unintegrated finite-tested primitive and supplies no additional resource savings to this checkpoint.
