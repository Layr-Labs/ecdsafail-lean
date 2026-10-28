# Shared-scratch blocked zero detector

`BlockedZero.chunks` accepts a list of `(flag, input wires)` blocks and a separate scratch list. Each block pairs its input wires with the prefix of the same scratch list. `Fits` requires each block to fit that list; `chunks_inputs` proves no input is silently truncated by the zip.

`program c target (chunks xs scratch)` computes each controlled block conjunction into its flag, recurses using that flag as control, then runs the same block detector again to clear the flag. Each invocation of the existing measured zero detector restores its scratch and phase. Cleanup uses fresh measurement outcomes in forward program order, rather than reversing a measured program.

`chunks_run` proves for every initial state and every measurement tape that the only final change is

```
target := target XOR (c AND (regValue (xs.flatMap Prod.snd) = 0))
```

All flags and shared scratch start at zero. The control and target may start at either value. Phase, inputs, flags, scratch, and every outside wire are restored. For a signed two's-complement row, the existing `Paper935.signedRegValue_zero_iff` identifies this predicate with signed zero.

`Valid` records local wire separation. In each block, its control, flag, input wires and scratch wires are distinct; the final target is outside them, and the flag is outside all later blocks. The recursive condition uses that flag as the next control. Scratch may occur in multiple blocks; no global distinctness requirement prohibits that intended reuse. `chunks_physical` derives ordinary-gate validity from this condition.

`chunks_support` bounds the emitted instruction list by the explicit input wires, flags, shared scratch, control and target. With N input positions, B blocks, and S scratch wires:

- Toffoli count: exactly 2N.
- Measurement count: exactly 2N, with corresponding phase corrections.
- Total distinct wires: at most N + B + S + 2.

Thus a 256-bit row split into at most 43 blocks of at most six inputs uses at most 307 wires including the input row: 43 flags, six shared scratch wires, and control/output ports are additional. `six_bit_qubits_le` proves that bound. Other block sizes use the same API; for example, 16 blocks of 16 inputs give a bound of 290 total wires. These are detector-local bounds, not a proof of the complete 935-wire schedule, and the implementation is not claimed to match the paper's gate count.

The walk owner must supply the actual input partition, distinct flag allocation, shared scratch allocation, and `Valid`/`Fits` proofs, then replace the old zero test in the post-step circuit. No change to the existing `ZeroLatch` implementation is asserted by these modules.

## Freeze/post-stage integration

`Paper935.BlockedPost` now supplies actual `zeroLatch`, `zeroFreeze`, and `publicPost` programs using the blocked detector. Pass `BlockedZero.chunks xs scratch` as their block list; `chunks_clean` derives their clean-work premise from the separate flag and scratch initial conditions, and `chunks_inputs` identifies the tested physical row.

`publicPost_spec` preserves the former post-stage contract: activity, zero witness and fire are cleared; frozen becomes old-frozen OR the armed zero predicate; the offset record is XOR-updated only at the first armed zero; phase and every wire outside activity/frozen/record are restored. The early, unarmed branch only retires activity. The existing offset ordering and initially-unfrozen record-zero premises remain explicit.

`publicPostInverse` first recomputes a retired fire from the frozen flag and offset record, then undoes the latch while reconstructing/clearing the zero witness with the actual blocked detector. `publicPost_roundtrip` proves exact restoration of the entire initial state for independent forward and inverse tapes. Only the measurement-free activity gates are reversed; measured detectors are run again in forward order with fresh outcomes.

The same namespace provides `post_physical` for both emitted programs, `shared_post_support` for their actual wire sets, and `shared_post_qubits` for the bound

```
N + B + S + 2R + 6
```

Here N is the tested row length, B the block count, S shared detector scratch, and R the offset register length. The six ports are one, zero witness, frozen, fire, activity, and comparison witness. The bound includes inputs and offset storage, not just extra scratch. Shared detector scratch is counted once. Record comparison retains its existing R-bit work allocation.

When armed, the forward post uses `4N + 1 + 2R` Toffolis and `4N + 2R + 1` measurements; its inverse uses `4N + 1 + R` Toffolis and `4N + R` measurements. Both counts are zero when unarmed. These are proved for the actual programs. Connecting them to the full finite walk and proving its peak-live bound remains a separate obligation.
