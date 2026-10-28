# Exact direct first native prefix checkpoint

Verified source: `3c31b172c158e2061628ae5d4c8352a2d3acfabd`. The change replaces the literal seed and first native tick, together with their inverse, in both arithmetic stages. The remaining 511 native ticks, delayed history codec, exact field cells, and point-corner/control/work contract retain their prior behavior.

| Scope | Toffolis | Measurement instructions | Allocation ceiling |
| --- | ---: | ---: | ---: |
| Stage 2 division | 1,054,514 | 724,538 | ≤1,899 |
| Stage 5 multiplication | 1,054,514 | 724,538 | ≤1,899 |
| Full finite-addend controlled point addition | 2,218,404 | 1,557,932 | ≤1,899 |

These are formal resource theorems. The ceiling bounds distinct allocated logical sites and therefore the stated schedule's peak; it is not an exact measured peak or a globally minimal allocation. No Q reduction is credited. The ≤1,297 Q / <600,000 T per-stage targets remain open.

With canonical divisor x and e=x mod2, the exact first tick writes H=floor(x/2)+e*(p+1)/2 and K=p+floor(x/2) for even x, or (x-p)/2 for odd x. Its transcript bits are G=!e and S=e. The original x word is transformed explicitly. There is no free erased input copy. The H update skips three known zero low constant bits; the K tail uses its unchanged low bit as carry-in before the final low-bit flip. Each independently emitted prefix direction costs 508 T and 508 measurements, replacing 771 T and 514 measurements. Thus each stage saves 526 T and 12 measurements.

`NativeFirstDirectReferenceEq` proves equality of the complete old/new prefix States for independent measurement records. `NativeFirstDirectCallerStates` proves the complete field-containing arithmetic caller with its original strong specification. The production controlled wrapper, point placement and full point-addition composition then use that caller. `ControlledPointAddSpec.lean`, `PointAddSpec.lean`, and `Math/AffineFormula.lean` are byte-identical to the protected earlier checkpoint.

## Verification

All Lean execution occurred on the CPU pod. The full library build completed in 815s with 3,969 jobs. The first audit failed in 3s because `NativeFirstDirectCallerSupport.olean` had not been included in the selected build targets. This was a verification-script omission. The next commit adds that target to both standard and timed verification commands without changing Lean source.

The successful attempt completed 3,970 build jobs in 7s, reusing the compiled library and compiling the remaining support module. It then passed all 1,572 public transitive axiom queries, representing 1,571 distinct declarations, in 242s. Final attempt total: 249s. The preceding main build plus supplemental build and successful audit total 1,064s, excluding failed audit and preparation/transfer time. Setup and queue time were zero. All 877 source hashes matched before and after the successful check; only `propext`, `Classical.choice` and `Quot.sound` occur in the audited closures.

The machine-readable [receipt](EXACT_NATIVE_FIRST_PREFIX_20261007.json) retains exact per-attempt timestamps and timing scope. Reproduce with `bash scripts/verify.sh` or `bash scripts/verify_timed.sh <log-directory>` on the authorized CPU pod. This is a formal all-valid-input monomial/phase proof, not correctness sampling.
