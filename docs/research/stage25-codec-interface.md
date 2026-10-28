# Exact compressed-history caller interface

This checkpoint adds reusable transcript-compression proofs. It does **not** select a new division, multiplication, or point-addition circuit. Production remains the exact point circuit verified at source commit `9ea2e58`: 2,740,035 Toffolis, 2,081,591 measurements, and ≤2,579 static logical sites.

The codec comes from `codec_synth.rs` at incumbent source `3161bd2058c63e883f2e12ffe8849cdd118513cd`. A legal symbol uses two bits with their AND equal to false. The existing `SkywalkTrace.trace_ternary` theorem proves this property for the exact GCD transcript.

| Operation | Toffolis | Measurements | Static component sites |
|---|---:|---:|---:|
| Encode three symbols | 3 | 1 | 6 |
| Decode three symbols | 4 | 0 | 6 |
| Decode, apply a field window, re-encode | Body count + 7 | Body count + 1 | Depends on body |

Encoding cleans the fourth caller site, leaving five sites holding the compressed word. The six-site support includes all raw input and decoder output sites. It is not a five-qubit peak claim. No additional quantum scratch is used by the codec.

`WireRename.lean` transports instructions, measurement corrections, support, resource counts, basis behavior and phase through an injective wire relabeling. `TranscriptCodec3.lean` lifts the finite gate check to arbitrary surrounding state and arbitrary measurement-record lists. `TranscriptCodecPlacement.lean` places the component on six distinct caller sites above the local template labels, proves full caller-state restoration, and provides the decoded field-window interface with independent records for encode and decode.

All three modules passed strict remote Lean compilation. All 22 public transitive axiom queries passed using only the permitted foundational axioms `propext`, `Classical.choice`, and `Quot.sound`. No arithmetic correctness axiom or sampling assumption was introduced. Source hashes matched before and after verification. The successful component build was 38.063 s. A corrected audit parser then rechecked the same compiled sources in 6.048 s, for a matched build-plus-successful-audit total of 44.111 s. The separate audit attempt did not rerun the already successful build. Its verifier setup and queue times were zero.

Verification evidence is retained in the workspace under `outputs/lean-stage25-exact-20261004/caller-verification/`; authoritative pod logs are `/root/ecdsadd-exact/logs/stage25-codec-interface-audit-v2` for compilation and `/root/ecdsadd-exact/logs/stage25-codec-interface-audit-v3` for the successful audit. Earlier failed proof and parser attempts are preserved.

## Scheduling constraint

The encoder can change the newest symbol's orientation bit. That bit remains a live input to the following integer tick. For a group starting at tick `j`, packing must wait until tick `j+3` has consumed the orientation from `j+2`. Reverse decoding must occur before reverse tick `j+3` reads it.

The exact signed-rail trace for the valid divisor `2^255` exhibits this issue at group start 255: raw bits `010000` encode to `111010`, changing the latest orientation from zero to one. The boundary divisor `p−1` also exhibits it. These deterministic diagnostics identify the scheduling obligation; they do not establish correctness of an integrated compressed loop.

## Remaining integration

The integer forward loop, reverse loop, and field replay still use raw history. They must adopt delayed packing, early reverse decoding and decoded field windows. Freed sites must then be reused in a proved allocation schedule. Compressing 512 symbols in triples would store 854 history sites instead of 1,024, but this is not a full-stage Q bound and does not establish the ≤1,297 target.

Stage 2 remains 1,315,329 T and Stage 5 remains 1,315,330 T, each with the existing ≤2,579 allocated-site ceiling. The ≤1,297 Q and <600K T targets remain active. Additional changes to field arithmetic, integer passes and routing are necessary.
