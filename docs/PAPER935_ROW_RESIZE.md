# Physical growth and reclamation of signed rows

The author's `WRow.grow` and `WRow.shrink` use one CX between a separate sign wire and a high value-bit wire. `Paper935.resizeBit` implements that gate directly.

`rowGrow_run` proves signed-value preservation when the new high bit starts zero. `rowShrink_run` proves signed-value preservation and actual clearing of the removed high bit when it equals the sign. Both preserve phase and all other physical bits. `rowShrink_bit_of_fits` derives the redundant-sign condition from the represented integer fitting the smaller signed window, rather than assuming the allocator can reset arbitrary data.

`rowGrow_reserved` obtains zero initialization and disjointness from `Arena.reserve`, assuming the old row and sign are owned. It proves readiness of the enlarged arena after the actual CX. `rowShrink_release` returns the cleared high wire through `Arena.release` and proves readiness afterward. Circuit support is checked separately by `resize_in_arena`; both the sign and high-bit addresses must belong to the arena. A release theorem by itself does not authorize an external sign wire.

Each resize uses one CX, no Toffoli and no measurement. No extra wire is allocated beyond the explicitly borrowed high bit. This handles a single physical resize, not the full allocator journal/replay, four-row host packing, stage schedule or point-add peak proof. It does not adopt the pending overall Framework specification or establish a failure probability.
