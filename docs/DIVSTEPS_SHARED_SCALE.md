# Modular scale removal in the measured shared-swap walk

`StepLayout.sharedScale` composes the physical shared-swap walk with modular
halving on the reverse pass. It preserves the input phase and every bit outside
the separate output accumulator. The active/parity history and all walk work
return to their input values; the single shared swap wire is measured and reused
at every forward layer, then reconstructed and cleared during reversal.

This extends the coherent-history `walkScaleUnwalk` component. It does not prepare
or copy the arithmetic endpoint into the output accumulator: that accumulator
still starts with a separately supplied canonical `r`. Global stopping,
provider/point integration, and paper-space claims remain open.

## Physical schedule

For each slot, the emitted recorded program is:

1. The actual `ForwardStep` on `L.sharedAt start`.
2. Bare X measurement of the one shared swap wire.
3. The recursive suffix, which returns its walk bits while updating the accumulator.
4. `reverseHalf` controlled by this slot's retained **actual active bit**.
5. Swap reconstruction from active and the updated coefficient bit, followed by
   the phase correction referencing the absolute ordinal from step 2.
6. The constructive measured inverse of the slot.

The recursive suffix and halving may consume arbitrary measurements. Recovery
uses the original swap outcome, not the current cursor or an inverse outcome.
`sharedScale_wellFormed` proves every deferred reference precedes its use.
Semantics hold for arbitrary input phases and tapes, including empty/short tapes.

## Proof interfaces

- `deferredSwap_frame_gap`: recovery only requires its three operands and pending
  phase to be restored by the gap. Other bits may change. The conclusion retains
  those changes and writes back the reconstructed swap.
- `StepLayout.swapAround_run`: lifts this to an actual step, recorded gap,
  recovery, and constructive inverse. With output wires disjoint from the step,
  every nonoutput bit and the original phase are restored. Output bits equal the
  gap's output. The inverse comparison uses measured-program locality, including
  immediate phase corrections.
- `StepLayout.swapScaleStep_run`: concrete single-slot instantiation with physical
  controlled modular halving. The active control comes from `program_zSlot_controls`.
- `StepLayout.sharedScale_run`: recursive finite schedule, using `SharedReady`,
  per-slot signed-width safety, enough finite history, a canonical accumulator,
  clean accumulator work, and disjoint valid accumulator wiring.
- `reverseSlotHalves_eq` and `reverseSlotHalves_zero`: connect the scalar recursion
  to `halveActive` over the reversed mathematical activity sequence. No external
  activity list or quantum scale counter is assumed.
- `StepLayout.sharedScale590_run`: discharges all signed-width fits for canonical
  256-bit inputs with walk widths 258/592/11 and 590 available history slots.
- `StepLayout.sharedScale_remove_scale`: if a first stopping index and the scaled
  accumulator relation are supplied, proves the resulting field value is the
  desired target. Those two premises remain explicit.

## Resources and limits

For `N` slots, integer/coefficient/counter widths `n/v/k`, and accumulator width
parameter `a`:

- T count: `N * (2*(5*n + 5*v + k - 4) + 1 + (3*a + 2))`.
- Measurement count: `N * (2*(4*n + 3*v + k - 5) + 1 + 2*a)`.
- Quantum support is contained in `L.sharedUsed ++ U.wires`.

At 590 slots and widths 258/592/11/256 these are **5,478,150 T** and
**3,623,190 measurements**, exactly 590 more of each than the coherent-history
PR99 program. These additional operations measure and reconstruct each swap;
this is not a claim of an overall resource saving.

`sharedScale590_qubits` proves the bound **4337 + U.wires.length**, under the
stated walk pool capacities. The accumulator includes its full modular arithmetic
work allocation. It is not included in 4337, and no 2613-wire or paper-space
bound is claimed. The active and parity histories remain coherent during the
forward pass, and are cleared by the inverse. No allocator for the combined
walk-plus-accumulator is constructed here.

All 20 new public theorem entry points are included in `scripts/verify.sh`'s
exact axiom whitelist audit. No new axiom, admitted proof, native decision proof,
or proof-resource increase is introduced.
