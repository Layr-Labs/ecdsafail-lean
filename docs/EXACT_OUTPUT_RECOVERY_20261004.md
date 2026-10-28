# Exact fused output recovery

Verified source: `9ea2e58e077e02b0525cb3947492d3246b2b18fd`. The complete controlled point-addition circuit passed the full CPU pod build and971 public transitive-axiom queries. All487 committed source hashes matched before and after verification; the public controlled-point specification file is byte-identical to the preceding checkpoint.

| Scope | Toffolis | Measurements | Logical Q certificate |
| --- | ---: | ---: | --- |
| Step6 output recovery | **2,301** | **2,301** | **≤1,036 allocated stage sites, including521 residents** |
| Full finite-addend controlled point addition | 2,740,035 | 2,081,591 | ≤2,579 static support sites |

Step6 meets Q<1,297 and T<8,000. The stage certificate is an achievable peak-live ceiling, not a measurement of the exact or globally minimal peak. Full-circuit exact live peak remains unmeasured. The complete model is the repository's signed-basis/fixed-record semantics described in PROOF_SCOPE.md; no full quantum-channel extension is claimed.

The exact x update fuses reflection and classical correction: when enabled, X←p−1−X followed by adding x_A+1 modulo p gives x_A−X modulo p. This handles zero and x_A=p−1 without an extra zero detector. The y update adds−y_A modulo p. The same stage is the selected suffix of pointDialogGeneric; cost is not moved into multiplication.

| Recovery operation | T | Measurements |
| --- | ---: | ---: |
| Conditional canonical x reflection | 255 | 255 |
| Controlled x_A+1 correction | 1,023 | 1,023 |
| Controlled−y_A correction | 1,023 | 1,023 |
| Total | 2,301 | 2,301 |

Constant addition reuses a256-site source bank,256-site carry bank and3 flags:515 shared scratch sites. Classical loads/unloads use Clifford gates. Together with521 resident point/control/classification sites the stage allocation is1,036. Each operation formally restores all non-output sites and phase for every record before reuse.

Compared with the preceding verified Step6, T falls5,884→2,301 (−3,583;60.89%), measurements4,604→2,301 (−2,303), and the Q ceiling1,550→1,036 (−514;33.16%). Full T falls2,743,618→2,740,035, and full measurements2,083,894→2,081,591. Step4 remains99,902T/99,382M/≤1,297 allocated sites. Narrow constants also give stages1 and3 the same≤1,036 allocation ceiling; T/M are unchanged there.

## Incumbent inspection

Public HEAD3161bd2058c63e883f2e12ffe8849cdd118513cd was fetched read-only and pinned. `classical.rs::coord_rsub` folds classical offset+1 into complemented reverse subtraction; the installed recipe sets BACK_SEAM_FUSE=3 and R4_YFIN_FUSE=1. Some recovery work is therefore fused with the multiplication endpoint, making standalone stage tags an imperfect conceptual decomposition.

This port adapts the exact complement/offset fusion and workspace reuse. It keeps full-width canonical arithmetic. The source's truncated fold and comparison windows are excluded without equivalent universal certificates. Current source inspection is not a rerun benchmark or a fresh leaderboard score certificate; older326-T stage numbers came from799153a.

Sources: [classical recovery](https://github.com/Layr-Labs/ecdsafail-challenge/blob/3161bd2058c63e883f2e12ffe8849cdd118513cd/src/point_add/classical.rs), [fused seams](https://github.com/Layr-Labs/ecdsafail-challenge/blob/3161bd2058c63e883f2e12ffe8849cdd118513cd/src/point_add/back_seam.rs), [arithmetic windows](https://github.com/Layr-Labs/ecdsafail-challenge/blob/3161bd2058c63e883f2e12ffe8849cdd118513cd/src/point_add/modular.rs).

## Verification

Full `lake --wfail build`:165s,3606 jobs. Public transitive-axiom audit:135s,971 queries, whitelist only propext/Classical.choice/Quot.sound. Total300s (5m). Queue and verifier setup0s. Source487 hashes matched. Evidence: `docs/verification/exact-recovery-20261004/`. All Lean execution was on216.243.220.86:14114, project/root/ecdsadd-exact/ECDSAAdd, logs/root/ecdsadd-exact/logs/step6-fused-recovery-v1.
