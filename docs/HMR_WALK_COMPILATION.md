# Explicit Hmr parameter compilation

The existing `compileAuthorWalk` uses a seven-bit signed counter and stores
history at threshold seven. Its schedule data comes from the pinned author's
Hmr schedule. It remains unchanged; its existing certificates do not establish
that it implements `circuit.py`'s `HmrWalk` gate sequence.

This change adds `compileHmrWalk`: a six-bit signed counter, six offset bits,
and history threshold five (coefficient bits one through four). The parameter
source is `engine.py` in the author checkout at
`64b5a13aa249f1360846657392e6c66817b26d0f`: `_jflags` lines 1466–1483,
history storage lines 1622–1629, and `hmr_composed_params` lines 3398–3431.
The 533-step public schedule is reused.

`compileHistoricalSlotWidth` and its checked wrapper parameterize the physical
coefficient slice. Width six is definitionally the previous slot compiler,
as proved by `compileHistoricalSlotWidth_six`. The generalized static budget
proof constructs successful checked slots, carrying persistent ownership,
distinctness, history growth, and row widths between steps. The original
instruction checker still checks the generated gates.

`hmrHistoricalBudgets` is checked by kernel reduction of the public numerical
schedule. `compileHmrWalk_exists` derives actual successful compilation of all
533 steps from those budgets and concrete seed geometry; it does not assume
that the compiler succeeded. `hmrWalk_dials` records the counter and offset
widths and the seed's 793 live addresses.

This is a parameter-instance and compilation certificate. It is not a proof
of literal source gate equality: Hmr's shared jflags and cached decoder chains
still need a corresponding implementation and proof, including depths two
through four. Full forward/reverse semantics, updated failure events, and
the full source-level resource certificate remains open. In
particular, the old 907/28 and 620/315 resource figures must not be assigned to
this new instance or to the source circuit.

## Persistent exit and retirement layout

The actual successful `compileHmrWalk` return now has a certified live-set
cardinality of 906, leaving 29 arena wires outside that live set. The proof
uses the actual compilation result and per-step geometry, not only a scalar
schedule calculation. The final row payload widths are 3, 4, 280, 280 and the
rows remain distinct and owned by the returned arena.

`hmrClosedArena` retires the 287 f/g/gv payload wires from this exit layout.
Its live-set cardinality is 619, with 316 wires outside it. This is the
retirement layout calculation. Executing the closer safely still requires
the generic closer's successful-input conditions (g=0, |f|=1, gv=f*p) and
entry readiness. These conditions have not been derived here from the new
whole-walk semantics. No full Hmr source-gate equivalence or whole-point-add
935-wire theorem follows from these cardinalities.

## Shared source anchor flags

`HmrFlagCell`, `HmrFlagChain`, and `HmrFlags` implement the actual shared
anchor split in `engine.py:1466–1499`: three AND anchors interleaved with
six CX gates, followed by the source release order and measurement-conditioned
CZ corrections. The six temporary wires hold j2/a1/j3/a2/j4/j5p; they share
the intermediate prefixes a1 and a2. The public forward theorem gives all
six values, and the complete release theorem restores the entire input
state, including its phase, for every measurement tape. Initial distinctness
and six clean scratch wires imply the staged readiness conditions.

This block uses three Toffoli gates and consumes three measurements on
release. It has not yet been installed into `compileHmrWalk`. The source's
cached decoder cube chains, physical allocation, and the complete walk
correspondence remain open; these standalone flag proofs do not close them.
