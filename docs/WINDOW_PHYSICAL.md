# Physical validity of the windowed arithmetic step

`WindowRoutedPhysical` and `WindowStepPhysical` certify the actual gate lists
from `WindowRouted` and `WindowStep`, in both directions. Inverse measurements
remain fresh measurements; these results do not replace measured programs by
reversed lists.

- `RoutedBankLayout.physical`: `Valid` implies `GatePhysical` for `program` and
  `inverse`. No state, tape, clean-work, or arithmetic-success premise is needed.
- `inverse_wires`: both directions have exactly the same physical support.
- `support`: the existing three arena membership conditions for routed arithmetic
  imply arena support in both directions.
- `counter_both_physical`: address uniqueness implies ordinary-gate legality for
  the counter update and its implemented inverse; no counter value assumption.
- `windowStep_physical`: combine `Valid`, `after.Planned`, and counter uniqueness.
  Resizing legality comes from the allocator's proved `ProperProgram` result.
- `windowStep_support`: combine routed support, `after.Planned`, counter address
  membership, and the existing counter length conditions. This includes the
  resize workspace and inverse counter workspace.

Apply `arena_program_qubits` to either returned support inclusion to obtain a
local bound of 935 physical addresses. This is conditional on actual address
membership in the arena, not a proof that the entire walk, history restoration,
or point-add implementation fits. The caller must still establish its concrete
layout, allocation, record-reference legality, and successful execution facts.

## Complete slot composition

`WindowSlotPhysical` extends these results to PR147's actual control preparation,
swap retirement/reminting, and blocked freeze/offset programs:

- `mintControls_physical` certifies preparation and its unmeasured reverse from
  the tag-address uniqueness and frozen/activity separation already used by the
  interpreter proofs. `mintControls_support` lists every touched address.
- `retiredWindow_physical` combines that preparation with `windowStep_physical`.
  The inverse's swap remint additionally requires the output coefficient's
  second wire to differ from the swap target.
- `WindowPostLayout.physical` derives both-direction gate legality from the
  existing `WindowPostLayout.Valid`; `support` includes comparison witnesses,
  probe flags/work wires, and record inputs/work wires via `ports`.
- `windowSlot_physical` certifies the entire implemented forward and inverse
  slot under these concrete layout conditions, with no input-state or tape
  assumptions.
- `retiredWindow_support` combines the two step support bounds with the actual
  preparation/swap-read addresses; `windowSlot_support` adds the post-layout
  ports. Apply `arena_program_qubits` for either local slot bound.

The support composition deliberately preserves the caller's allocation
obligations. In particular, membership of the second coefficient wire and all
post-processing scratch is required rather than assuming a read from an
unallocated address. History transport and the full walk remain separate.
