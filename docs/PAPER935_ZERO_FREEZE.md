# Activity and actual zero-triggered freeze

`mintActivity` computes the activity bit from the persistent frozen flag. After the latch changes the flag, `retireActivity` uses the retained fire bit to clear the old activity. The latch establishes that cleanup predicate; it is not an independent correctness assumption. These operations use only X/CX gates and no additional workspace.

`zeroLatch` computes a zero predicate from the actual physical g-row inputs using `equalConstant`, applies the freeze latch and retires activity, then recomputes the predicate to clear its witness. `signedRegValue_zero_iff` proves that the physical test is also exactly the signed integer zero test. The output flag and offset are derived from those row bits.

`zeroFreeze` then clears fire using the post-state flag and stop offset. The existing strictly-older-offset invariant gives `fire = frozen AND record=currentOffset`; this needs no retained zero witness. A comparator controlled by a physical one bit and the existing measured AND cleanup restore fire, the comparison witness and its workspace for every measurement tape.

`zeroFreeze_spec` proves the entire post-stage state relation: phase preserved, activity/zero witness/fire cleared, frozen flag updated by actual row zero, record XOR-written only on the first freeze, and every other physical bit restored. Its inputs include an old activity bit consistent with the old flag, clean scratch, disjointness conditions, a representable public offset, record<currentOffset, and an unset record on active lanes. The one control must physically contain true.

## Resources and limits

For g-test width n and stop-record width r, this implementation uses `2*n+1+2*r` Toffolis and `2*n+2*r+1` measurements. For r=6 both are `2*n+13`. Activity generation/retirement adds no Toffoli or measurement. Support theorems enumerate the actual wires.

The zero test allocates one clean work bit per tested g bit. Record comparison similarly needs r clean work bits. The two phases do not require their workspace sets to be mutually disjoint, but reuse must satisfy the concrete cleanliness and separation premises. This is a recomputed-comparator implementation, not the author's optimized blocked-zero/retained-trail circuit. No 935 peak-live or paper gate-count claim follows yet.

`publicPost` adds the public early no-test interval: before arming it only retires activity; once armed it runs `zeroFreeze`. Its offset-capacity and strictly-older-offset hypotheses are conditional on arming, so an early public offset of zero is allowed. `pinStep_flag_record` matches the hardware flag/XOR-record formulas to the existing integer pin-step transition when the tested row is the post-arithmetic g.

Actual composition with the active/frozen arithmetic, row-width changes, branch-history storage and finite walk remains to be implemented. The latch-only `activityLatch` lemma tests the activity lifecycle without an arithmetic body between its endpoints; it is not a whole divstep theorem. Reverse lifecycle and endpoint/provider integration also remain open.
