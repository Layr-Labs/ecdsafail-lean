# Complete exact point circuit with compact raw guards

The **full controlled point-addition circuit** is Lean-verified at **2,853,821 static Toffolis / 2,194,105 measurements / at most 2,994 distinct static logical wire sites** for a finite classical addend. Peak-live qubit width remains unmeasured. The identity-addend program is empty.

This integrates the compact guards into both retained arithmetic endpoints, their actual instruction-support proofs, both complete 512-cell replays, division, multiplication, and the full controlled point circuit. It saves **2,560 Toffolis and 3,072 measurements** over the retained-both checkpoint. Relative to the original 7,207,866 Toffolis, the reduction is **4,354,045 (60.41%)**.

## Exact mechanism

A 257-bit raw word suffices for 256-bit field values under the true bound `2*p < 2^257`. Its top bit cannot simply be interpreted as a sign: positive inputs close to `p` can produce a sum above `2^256`. Instead, the circuit reconstructs the signed guard explicitly as `j = b AND h`, where `b` is the sign control and `h` the normalization flag. Field values retain all 256 bits. No input, comparison, carry, round or measurement outcome is omitted.

The independently emitted forward and inverse packed arithmetic streams each cost **1,538 Toffolis and 1,538 measurements**. Each routed cell adds 256 Toffolis for its controlled swap, for a total of **1,794 Toffolis**. `CompactGuardPackedForward.lean` and `CompactGuardPackedInverse.lean` prove the complete endpoint semantics. `CompactGuardSupport.lean` proves the support of the actual programs within the original shared pool. The protected public point specification remains byte-identical, including control, phase and complete workspace restoration for every measurement record.

| Complete point-addition stage | Static Toffolis |
|---|---:|
| Input and corner classification | 4,104 |
| Coordinate differences | 2,046 |
| Division | 1,315,329 |
| Add three times the addend x coordinate | 1,023 |
| Square subtraction | 210,105 |
| Multiplication | 1,315,330 |
| Final coordinate correction | 5,884 |
| **Total** | **2,853,821** |

## Verification evidence and timing

All Lean execution used the CPU pod, pinned Lean 4.28.0 and pinned Mathlib. The complete warnings-as-errors library check passed **3,518 jobs**, followed by **749 public axiom queries covering 748 distinct declarations**. The existing duplicated query remains. Transitive axioms are restricted to `propext`, `Classical.choice` and `Quot.sound`. All **411 captured source-file hashes** matched the pod before the subsequent Markdown-only documentation edits. The protected specification SHA-256 is `e3d4a181ad1e0e6d4458dc8bcc85d1de7d4ffd6c02c7ce11ee5a11296e08210d`.

The final successful check took **122 seconds: 2 seconds cached incremental full build plus 120 seconds axiom audit**, with **0 seconds queue delay**. This is not a cold-build measurement. The preceding attempt compiled the complete library in **95 seconds** and then failed its audit after 129 seconds because a legacy public declaration was no longer transitively imported by the root. An audit-only import of its original module repaired that visibility issue; all 749 checks were retained. Failed and successful attempts are recorded separately. Initial pod setup and baseline checks took 2,425 seconds and are excluded from these verification times.

Authoritative successful logs: `/root/ecdsadd-exact/logs/compact-guard-full-point-v2`. The campaign preserves timings, build/audit logs, the frozen source manifest and hash check under `skywalk/compact-guard/full-point/verification-v2/`. Failed-attempt logs remain under `verification/`.

## Remaining structural work

The planned retained forward and inverse integrations are complete. The in-place two-cell joint-recovery prototype was emitted and screened at 3,361 Toffolis with fixed controls and without the general routing wrapper. It exceeds the approximately 944-Toffoli target, so this emitter family is rejected. Its validation is a prototype check, not a Lean certificate or a production saving.

Reaching below 1.5 million still requires a materially different field-update mechanism. Next screens should examine carry-image sharing across updates and exact Boolean-prefix or measurement-absorption transformations in our own operation stream. Each must include independent measurement outcomes, phase correction, controls and complete cleanup before its savings are counted. Larger blocks are justified only after a two-cell mechanism passes the cost screen. Peak-live qubit accounting remains a separate task.
