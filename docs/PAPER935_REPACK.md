# Moving occupied row bits back into home hosts

`rehome` emits the author's three-CX swap to move an occupied overflow wire into a zero home-host slot. `rehome_run` transports every bit through the corresponding wire permutation and preserves phase. `rehome_row` preserves signed register values after updating row views. Distinct wire lists remain distinct, and applying the same relocation twice restores the entire state for independent measurement tapes.

`rehome_allocated` starts from an actual successful reservation of the destination, so the destination is provably zero. Both old and new sites are included in `during.live`; the transient peak is charged before release, not only afterward. The swap clears the old site, which can then be released. The theorem proves actual program support inside the transient live set, its bound of 935, and readiness after release.

`repack` and `unpack` replay a finite public relocation journal in forward and reverse order. The program-level theorems preserve signed row views and prove the complete roundtrip. They use zero Toffolis and zero measurements; bounded journal addresses imply support in the shared arena.

The caller must still construct the author's journal from host availability and certify each allocation transition. This change does not implement the complete four-row packing policy, prove every requested reservation succeeds, or certify the full point-add peak. Failure probabilities and the new overall specification remain separate obligations pending owner approval.

The executable `Arena.borrowFrom` selects the least free address in a band. `borrowFirst` tries bands in public priority order and is connected to the physical move by `rehome_selected`. Their contracts prove zero initialization and legal reservation. With the whole arena as a fallback band, `borrowFirst_fallback` proves success whenever fewer than 935 sites are owned; `borrow_capacity` gives the exact single-band success criterion. This compiler choice is not a measurement of whether a quantum datum is zero. Actual host preference lists and the complete schedule still need instantiation.
