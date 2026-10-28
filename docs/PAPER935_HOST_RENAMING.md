# Transporting endpoint certificates between host placements

The complete endpoint splice can now be relabeled without re-proving the walk. The full-restoration, fresh-output and already-owned-output certificates each transport to the actual renamed program, with the same tape and original absolute record cursor. Their input states and output specifications are pulled back along the placement; their arenas and output sets are mapped forward.

## Finite arena permutation and execution

A globally injective function from all natural-number wire addresses into 935 addresses cannot exist. The finite interface instead takes a map injective on `arenaWires` whose image is `arenaWires`. `finiteWirePermutation` extends that map by the identity outside the arena. `finiteWirePermutation_program` and `renamedEndpoint_ofFinite` prove that this extension emits exactly the same renamed instructions as the original map on an arena-supported program. There is no premise concerning the original map outside the arena.

The global extension is important for the full-state `pullState` theorem: an arbitrary outside address could otherwise alias an inside address. `ArenaPermutation` represents a wire permutation preserving arena membership; `ArenaPermutation.ofFinite` constructs it from the finite interface above. All endpoint transport theorems work for this representation.

Existing recorded renaming supplies exact support images, preserved T/M counts and unchanged classical record identifiers. `RecordedPermutation` adds well-formedness equivalence at the same cursor, unchanged interpreter cursor advancement, full-state restoration transport, output-image transport and clean-external-site transport. Immediate and deferred correction operands are renamed; classical measurement ordinals are not. No measured gate list is reversed.

## Actual allocator boundaries

`Arena.renamed` maps the live set. `renamed_card` preserves its size; `renamed_ready` is an equivalence with the pulled-back basis. `renamed_reserve` and `renamed_release` transport successful transactions, including the zero-bit checks at release. Images preserve support inclusion and disjointness.

`renamedEndpointClosed` executes the renamed seeded walk and closer. `renamedEndpointAfter` then executes the renamed E. Their pullback theorems connect these *actual executed states* to the original certificate boundaries. Consequently the transported transactions release against the actual physical output of E, not an independently supplied state.

The three transport theorems are:

- `endpointSlotCertificate_renamed`: full restoration, closer release/readiness, temporary borrowing and release, post-E readiness, and payload reclaim.
- `endpointOutputCertificate_renamed`: output on the image of O, newly reserved retained arena, temporary-only release, and the original combined output/workspace bound.
- `endpointOwnedOutputCertificate_renamed`: output on the image of O already owned in the closed arena, independent 256-output/315-temporary bounds, exact `during = 620 + temporary`, and final renamed-entry readiness.

Each returns `RenamedEndpointResources`: exact support image, addresses below 935, record legality, unchanged sources and counts, and the original additive segment counts. The certificates are premises at `pullState e s`, with output specification `v ∘ e`; their conclusions concern physical state s and physical output O.image e. This is a transport of all existing obligations, not a new correctness assumption or an implementation of E. The old fresh-output interface still cannot retain a nonempty fresh isolated output for this walk.

## Explicit y/A exchange

`swapYA` adds 256 on [256,512), subtracts 256 on [512,768), and fixes every other address. `swapYA_involutive` proves it is its own inverse. The `hostSwap` instance preserves the 935-address arena. Kernel-checked theorems establish:

| Original placement | Exchanged placement |
|---|---|
| g seed in x | g seed in x |
| f seed in y | f seed in A |
| Retained aHost in A | Retained host in y |
| Entry owned x/A | Entry owned x/y |
| Entry y must be zero | Entry A must be zero |
| Auxiliary addresses 768 onward | Same addresses |

`hostSwap_seed_rows`, `hostSwap_seedBefore` and `hostSwap_entry` make these mappings explicit. `hostSwap_output_isolated` proves that the retained **physical y host** is disjoint from the actual entire relabeled walk/closer/uncloser/reverse. The three `hostSwap_*_certificate` theorems instantiate all transport results.

This matches the x/A-row, y-retained placement in the storage-plan table. It does not move arbitrary pre-existing data by executing swap gates: it is a choice of physical layout with the corresponding transported entry conditions. Nor does it construct the caller stage that establishes those conditions, bind point-addition operands or outer controls, implement the fused endpoint, or close the full point-addition 935-wire and failure-budget claims. In particular, the relabeled retained output is y; forming a subsequent mathematical result in physical A is a separate stage obligation.
