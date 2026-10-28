# Output in the already-owned 256-bit host

`authorWalk_aHost_support` proves that `aHost = [512,768)` is disjoint from the actual seeded walk, endpoint closer, uncloser, and recorded reverse. It is a statement about emitted instruction addresses, including measurement corrections and the real history decoder. It holds for every modulus parameter and record ordinal whenever `compileAuthorWalk` returns the supplied slots. It needs no successful-input or decoder correctness premise.

The proof follows the actual compiler. A wire already owned outside the current rows, metadata and history cannot be borrowed as scratch. Row resizing keeps it owned and outside the new rows. The arithmetic front, post-processing, growing history and all five depth-decoder stages have support within their actual inputs and freshly borrowed sites. Induction threads this external-wire property through the historical walk and its actual reverse. Seeding and closing use only their explicit seed or row addresses. The proof does not infer syntactic isolation from final-state restoration, and it never reverses a measured gate list.

`authorClosedArena_aHost` proves all 256 host sites remain owned after closing. This resolves the owned-host placement question left open by the fresh-output certificates. It is consistent with `retainedOutputSpace_empty`: that definition excludes every exit-live address, including the host.

## Endpoint contract and conclusion

`EndpointOwnedOutputContract` allows `O ⊆ aHost`. It requires the actual supplied endpoint program E to be well formed at its record cursor, stay inside the arena, produce the declared bits on O, and satisfy `OutputUncloserReady` for all remaining state and phase obligations. The actual allocator transaction reserves and releases **only temporary workspace**. O is already owned, so reserving it again is neither required nor permitted by this interface.

`endpointSlot_withOwnedOutput` proves that executing the actual seeded walk, closer, E, uncloser and actual reverse returns `withOutput O v s`: precisely v on O, the original bits everywhere else, and the original phase. The return-stream isolation premise is discharged by the compiler theorem, not assumed from the caller.

`endpointSlot_ownedOutput_certified` also supplies record well-formedness, addresses below 935, exact additive Toffoli and measurement counts, output ownership, temporary release, readiness after E, and restored `seedBefore.Ready` at the final state. `endpointSlot_ownedOutput_bits` exposes the three phase/output/frame conclusions separately.

The storage equations are:

- `O.card ≤ 256`, with O included in the existing 620 closed-live sites;
- `temporary.card ≤ 315`, disjoint from O;
- `during.live.card = 620 + temporary.card ≤ 935`.

There is no `O.card + temporary.card ≤ 315` charge: that equation belongs to the different fresh-output transaction. No optimal endpoint workspace use or concrete E implementation is established here.

## Remaining physical point-addition obligations

The present seed uses x for g, y for f, and retains A. Its entry readiness allows data only in x and A; y must be zero. The uninstantiated storage-stage plan uses x/A for rows and retains y. An explicit stage rename or movement theorem is still needed to connect those roles. The walk's controls are not yet bound to the outer point-addition controls.

This result proves a legal preserved host placement. It does not specify A's mathematical contents, construct endpoint arithmetic, discharge point-addition entry clearing, bind outer controls, certify the supplied E's ordinary gate legality, or prove the full point-addition resource/probability bound. The fused endpoint versus inverse-plus-Montgomery choice remains separate. Global tasks 15/7 are not closed by this certificate.
