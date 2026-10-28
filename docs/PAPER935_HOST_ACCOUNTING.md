# Seed ownership and the whole-point-add resource boundary

This inventory describes the concrete seed layout on main at `3dbb46b6`.
The 935-address pool includes three proposed point-add hosts. The current
walk theorems do not yet bind those hosts to a complete point-add program.
A bound for this walk and its owned storage therefore does not establish the
whole-point-add resource bound.

## The 794 owned seed addresses

`AuthorWalkCompiler.lean` defines `walkSeedArena.live = range 794`.
Its allocation is:

| Addresses (inclusive) | Count | Concrete seed role |
|---|---:|---|
| 0–255 | 256 | `xHost`, input word and g payload |
| 256–511 | 256 | `yHost`, initially clean, loaded with p as f payload |
| 512–767 | 256 | `aHost`, caller-owned third word |
| 768–771 | 4 | f, g, fv, gv sign wires |
| 772–773 | 2 | fv and gv payloads, initialized to 0 and 1 |
| 774–780 | 7 | one, frozen, parity, active, swap, work0, work1 |
| 781–787 | 7 | signed counter |
| 788–793 | 6 | offset |
| **Total** | **794** | Owned wires, regardless of their bit values |

The history record is initially empty. Later history and arithmetic allocations
come from the same `arenaWires = range 935`; there is no external scratch pool
in this allocator. The 794 count is an initial ownership count, not a peak
or a complete point-add register inventory.

Before seeding, `seedBefore.live = xHost ∪ aHost` has 512 owned addresses.
`seedBefore.Ready` requires every other address in the pool to be zero,
including all of yHost. `seed_reserve` borrows yHost and six sign/coefficient
wires, obtaining 774 owned addresses. Metadata initialization supplies the
remaining 20 owned addresses for the walk.

`SeedEntryConditions.lean` makes this caller obligation directly reusable:
`seedBefore_ready_iff` is the equivalence with zero on yHost and on addresses
768–934. `seedBefore_ready_iff_word` replaces the yHost clause with
`regValue seedF s = 0`, keeping the auxiliary clause separate.
`seedBefore_ready_of_agree` proves that changing only x/A data preserves
these entry conditions. These theorems characterize the required input;
they do not supply a preceding point-add program that establishes it.

Thus the seed cannot directly accept arbitrary point coordinates in both xHost
and yHost. The caller must establish the required intermediate state: an input
word in xHost, its declared data in aHost, and a clean yHost. The seven walk
control/work wires are not a proved encoding of the outer point-add control.

## Host roles still require a stage binding

The intended, uninstantiated table in
[PAPER935_STORAGE_CONTRACT.md](PAPER935_STORAGE_CONTRACT.md) describes its first
walk with x/A carrying rows and y retained. The concrete seed instead places
rows in x/y and retains A. An explicit stage renaming or data-moving program,
with value, phase, ownership and cleanup proofs, must connect these roles.
The table is not such a proof, and the host names do not imply that connection.

[SCALING_CALL_SEEDS.md](SCALING_CALL_SEEDS.md) records mathematical point-add
call arguments. Those identities do not supply a complete physical binding
of the compact endpoint to the point-add adapters. In particular, the present
layout does not establish which point coordinate or intermediate value is in
A at each invocation, or where the outer control is kept throughout it.

## Existing owned hosts and new output loans

A is already owned at entry and is not part of the newly available output
space. The `retainedOutputSpace` interface excludes the exit live set by
definition. Its capacity bounds therefore do not exclude using an existing
caller-owned host after proving the necessary support and state contracts.
They also do not exclude implementations that touch output wires and later
preserve their values semantically.

`seed_run` proves that seeding preserves the third word. The stronger
`authorWalk_aHost_support` theorem now proves support separation for the
actual seeded walk, closer, uncloser and actual reverse walk, conditional on
successful compilation. `authorClosedArena_aHost` proves the host remains
owned after closing. These are compiler-derived support and ownership facts,
not inferences from final-state restoration.

The merged [owned-output interface](PAPER935_OWNED_OUTPUT.md) supplies
`endpointSlot_ownedOutput_certified`: under the stated walk premises and an
explicit `EndpointOwnedOutputContract` for E, the full program preserves the
phase and all bits outside O, while O receives its declared output. Here
O is a subset of A, with at most 256 sites. It is already included in the
620 owned sites; only temporary wires are reserved and released, with at most
315 such wires and `during.live.card = 620 + temporary.card ≤ 935`.
The supplied E must still establish its arithmetic output and cleanup
obligations. The theorem does not construct E or bind A to point coordinates.

Even with that interface, the following point-add obligations remain separate:

- Bind A's mathematical value and the input/g word to each actual call.
- Prove the preceding point-add stages establish yHost's required zero state.
- Bind and preserve the outer point-add control, including disabled calls.
- Prove the host-role changes, endpoint arithmetic, result consumption and
  final ancillary cleanup on the actual programs and every measurement tape.
- Cover every surrounding point-add stage and simultaneously live register
  in the same resource accounting.

These are integration obligations, not evidence that a whole-point-add
935-wire implementation is impossible. The present walk allocation alone
proves neither that impossibility nor the completed whole-machine bound.
