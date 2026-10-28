# Concrete row initialization

`Seed.lean` implements the author's `init_rows` seed pattern using a concrete bounded address assignment:

| Role | Physical addresses | Initial signed value |
|---|---|---|
| g payload | 0–255 | input word |
| f payload | 256–511 | p |
| preserved third word | 512–767 | unchanged |
| f, g, fv, gv signs | 768, 769, 770, 771 | zero |
| fv payload | 772 | zero |
| gv payload | 773 | one |

The initial ownership contains g and the third word (512 sites); all other arena sites must be clean. `seed_reserve` reserves the clean f word and six sign/coefficient sites. The resulting live set is exactly `range 774`, leaving 161 unowned sites inside `range 935`. This is a row-seed instant, not the full walk peak: z, record history, freeze machinery, and arithmetic transients are not yet allocated.

`seedRows p` emits constant X gates on the concatenated view `seedF ++ [773]`, loading `p + 2^256`. This is a convenient representation of the author's separate modulus X gates and unit-coefficient X gate. For every `p < 2^256`, `seed_rows` proves signed values `(f,g,fv,gv) = (p,input,0,1)`. `seed_run` proves phase preservation, preservation of every non-seed wire (including the third word), and final arena readiness. No canonical-input assumption is needed for this seed alone.

`seed_roundtrip` proves complete state restoration by the same X program. `seed_uninit` then proves release returns the exact original arena. The program itself has zero Toffolis and measurements and touches at most 257 wires; its occupied arena is 774 sites. These numbers have different meanings and must not be substituted for each other.

## Source and schedule correction

The checked source is `uncompute-paper/tasks/modinv-point-add/circuits/divsteps/engine.py`: `WRow` around line 371, `Schedule` around line 680, `_repack` around line 951, and `init_rows` around line 978. At the seed, f/g each need 256 payload positions and fv/gv each need one. Therefore each home pair initially exceeds its 256-site host by one, and the coefficient payloads must occupy extra sites. The earlier no-spill `pairedHosts 256 1 256 1` cannot represent this seed.

The author's widths, row allocation, and repack scan order are public compile-time schedules. “Dynamic straddle” describes compiler allocation of extra physical sites, not quantum-data-dependent addressing. Earlier component documents that exclude quantum-data-dependent selection must not be read as requiring such a mechanism to reproduce this algorithm. The outstanding task is to instantiate the public schedule, prove successful-lane numeric window/cleanup conditions, account for its full live peak, and bound the actual trajectory failure events. Sample-fitted windows are not probability theorems.

This seed is not yet integrated with the surrounding point-add stages or a full walk schedule. No probability bound or whole-point-add 935-qubit claim is made, and the pending Framework specification is not adopted.
