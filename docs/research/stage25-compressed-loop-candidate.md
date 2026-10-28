# Delayed compressed-history integer-loop candidate

The new executable integer-loop candidate inserts packing after ticks 3, 6, ..., 510 and decoding before those same reverse ticks. This packs groups beginning at 0, 3, ..., 507, leaving symbols 510 and 511 raw. Packing waits until the following tick has consumed each group's latest orientation.

The actual integer-state assertion now supplies the three-symbol codec's legal domain for every input in the existing exact GCD contract. A separate gate-support theorem proves that encoded groups commute with later forward ticks and decoded groups commute with later reverse ticks once `start + 4 ≤ tick`. Measurement corrections are included in the support and commutation proofs. Each block keeps its independent measurement record.

| Integer program | Static Toffolis | Static measurement operations |
|---|---:|---:|
| Existing forward pass | 197,632 | 98,943 |
| Delayed compressed forward candidate | 198,142 | 99,113 |
| Existing reverse pass | 197,632 | 98,943 |
| Compressed reverse candidate | 198,312 | 98,943 |

The candidate adds 1,190 T and 170 measurement operations across the two integer passes. These are formal instruction counts, computed from the constructed program without input sampling or physical execution. They are not average activated-gate statistics.

All four new modules passed strict component compilation. All 19 public transitive axiom queries passed against matching source hashes, with only the permitted foundational axioms. The matched successful component builds totaled 21 s and the successful audit took 6.456 s. Setup and queue time for the verifier were zero. Workspace evidence: `outputs/lean-stage25-exact-20261004/compressed-loop-verification`; authoritative pod audit: `/root/ecdsadd-exact/logs/stage25-compressed-loop-audit-v1`.

This is a candidate. The full forward-loop compressed-state invariant, full reverse restoration, decoded field replay and physical scratch reuse still need composition proofs. The support and local codec proofs do not establish complete-loop correctness or a full-stage qubit reduction by themselves.

The selected point circuit is unchanged at source checkpoint `9ea2e58`: 2,740,035 T, 2,081,591 static measurement operations, and ≤2,579 static logical sites. Stage 2 and 5 targets remain ≤1,297 Q and below 600K T if possible. No candidate savings have been promoted.
