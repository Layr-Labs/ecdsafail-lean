# Exact measured streamed square: integration checkpoint

Lean source commit: `88aad071b739086e04a9ed46693b4f97bb4cd71c`. The complete remote build and all931 public transitive axiom queries passed. Resource figures below are the verified integrated theorem statements.

The selected `pointDialogSquare` now calls `pointMeasuredSquareCandidate`, whose complete emitted program is proved in `MeasuredStreamedSquareProof.measuredProgram_correct`. This is the full Step 4 and is selected in the complete controlled point-addition circuit. Correctness is a formal proof in the repository's signed-basis/measurement-record semantics, for every 256-bit source, canonical output and every measurement record. The square stage restores every non-output wire and phase. The public `controlledPointAdd_spec` statement and source are unchanged, including all valid point inputs, doubling, inverse points, infinity, control restoration and zero workspace.

## Resources

| Scope | Toffolis | Measurements | Logical Q certificate |
| --- | ---: | ---: | --- |
| Selected complete Step 4 | 99,902 | 99,382 | ≤1,297 allocated stage sites, including residents |
| Complete finite-addend controlled point addition | 2,743,618 | 2,083,894 | ≤2,579 static logical support sites |

The Step 4 allocation certificate provides a peak-live ceiling. It does not establish the exact or globally minimum peak. The full-circuit support bound is also a safe allocation ceiling, rather than a newly measured exact live peak. The other arithmetic stages still dominate full-circuit Q.

## Complete emitted Step 4 budget

| Component | T | Measurements |
| --- | ---: | ---: |
| Three raw square producer/independent-cleanup pairs | 50,558 | 50,558 |
| Controlled input masks, erased and recreated | 770 | 770 |
| Sum preparation/restoration | 512 | 0 |
| 38 exact canonical modular-add updates | 38,874 | 38,874 |
| Four full-source normalization/undo pairs | 4,088 | 4,080 |
| Twenty retained-output reflections | 5,100 | 5,100 |
| Total | 99,902 | 99,382 |

The masked source carries the quantum control. There is no blanket control wrapper over the arithmetic gates. Literal and complemented source bits are read directly, avoiding separate constant and diagonal mask registers. Square leaves are produced, folded into the output and independently cleaned before the next leaf. Carries and measured masks are discharged with immediate Clifford corrections for every record; measurement streams are never reversed.

Canonical leaf and rotated-square sources are justified by universal arithmetic lemmas. The four other full-word rotations retain exact 256-bit source normalization. No probabilistic fold window, truncation, approximate arithmetic or sampled-input envelope is used.

Compared with the prior verified low-width checkpoint `d477a67`, Step 4 saves 649,436 T (86.67%): 749,338 →99,902. The complete point circuit saves the same non-overlapping 649,436 T: 3,393,054 →2,743,618. It uses 99,382 more measurements.

The older signed-row checkpoint remains a separate lower-T/higher-Q tradeoff: Step 4 82,101 T /81,589 measurements /2,865 schedule-peak Q; full point 2,725,817 T /2,066,101 measurements /≤2,994 static support. This new low-width circuit uses 17,801 more total T than that older checkpoint. Its purpose is to meet the ≤1,297-Q square-stage ceiling while keeping T below100K.

The pinned incumbent Step 4 comparison remains 41,150 static T /1,174 reported peak-live Q. Our Q value is a conservative formal ceiling and its T is a fixed exact gate count; those resource definitions should remain visible when comparing.

## Verification evidence

All Lean execution uses the CPU pod at `216.243.220.86:14114`, project `/root/ecdsadd-exact/ECDSAAdd`. The selected source manifest contains480 committed Lean/build/script files. The unchanged original public audit was expanded with182 new Step4 declarations, for931 public transitive-axiom queries. The whitelist remains exactly `propext`, `Classical.choice`, `Quot.sound`.

The first full-run preflight stopped before Lean execution because `scripts/verify_skywalk.sh` on the pod differed from the committed source. The script was synced and a new logged attempt was launched. The successful second attempt completed3599 build jobs and all931 axiom queries:355s build +138s audit =493s (8m13s). Queue and verifier setup time were0s. All480 source hashes matched before and after verification. The original controlled-point specification file was byte-identical. Repository evidence is saved under `docs/verification/measured-streamed-99902-20261004/`.
