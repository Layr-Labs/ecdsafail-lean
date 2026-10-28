# Swap-tag retirement in the actual slot

`taggedStep_divstep_controls` and `slotBody_controls` retain the actual output q/parity formulas alongside the previous row/frame conclusions. The old public theorem signatures remain unchanged through wrappers.

`retiredBody` appends a measured AND erasure of q, corrected by CZ on old activity and the updated coefficient row’s second bit. The reachable-state invariant `Inv p st` and odd p imply that this coefficient bit reconstructs the swap branch on active inputs; frozen inputs have g=0 and q=0. The exact all-tape result is the original arithmetic body output with q cleared and phase unchanged.

`retiredSlot` runs this retirement before the public freeze post-stage, while old activity is still available. It proves the same five-field, frozen and stop-record `pinStep` relation, now with q, active, zf and fire cleared. The extra measurement advances the tape before subsequent post-stage measurements; the proof composes at that actual cursor. No outcome distribution assumption is used.

Retirement costs zero additional Toffolis and one measurement. Its correction reads existing activity and fv wires; support is explicit. `Inv p st`, signed fit bounds, clean work and static alias/record exclusions remain hypotheses to discharge in a concrete trajectory/layout.

Parity is still retained. Selective history storage, forward measurement/reverse parity correction, row resizing, the finite compact inverse/walk, and 935 peak-live and numerical failure bounds are not completed here. This change is not a substitute for those obligations.
