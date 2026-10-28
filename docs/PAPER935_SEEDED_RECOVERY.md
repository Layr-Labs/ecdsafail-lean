# Seed cleanup and connected decoder inputs

`seededAuthorWalk_reverse_of_history` composes the actual seed gates, actual 533-slot forward walk, conditional actual recorded reverse walk, and actual seed cleanup. The result restores the entire input State, including phase, for every measurement tape and original/reverse cursor satisfying the stated history conditions.

Its premises are exactly:

1. A finite original input-label type with decidable equality, an integer input map, and one label.
2. A natural modulus p below 2^256 whose integer value is odd.
3. The original label is outside `authorTrajectoryEvents input p`. This is the existing joint numerical/early-zero/deadline failure event, not an assertion that every legal label succeeds.
4. The actual `compileAuthorWalk` returns the specified slot list (existence is proved separately without numerical state assumptions).
5. The initial physical state satisfies `seedBefore.Ready`, and the integer value in `seedG` equals the label's input value.
6. A supplied decoder family and `WalkHistoryUndo` for that family, actual slot list, same global tape, forward cursor, reverse cursor, and actual seeded state. This substantive premise requires each history recovery to restore its actual pre-history state, including phase. It retains original measurement source indices and accounts for every measurement in the emitted reverse tail. Decoder construction, cleanliness, finite capacity and its numerical assumptions must discharge this predicate independently.

There are no per-step arithmetic inverse premises: the preceding arithmetic-undo theorem derives them from the same good event and actual forward states. The seed inverse is explicitly `seedWalkMetadata ++ seedRows p`; its full-State roundtrip holds on arbitrary tapes. No gatewise reversal of measured operations is used.

`WalkForwardInputs` records each actual boundary's arena, bank, metadata and history integer recursively. `compileHistoricalWalk_inputs` and `compileAuthorWalk_inputs` derive this predicate. `walkForwardInputs_prefix` exposes the invariant after any actual `slots.take i`, with every returned view taken from that exact compiled prefix. These are intended inputs to the concrete history decoder proof.

This roundtrip does not copy an inverse result to an output or implement final modular scaling. It is conditional on history recovery, and supplies no unconditional inverse endpoint, whole-machine 935-wire bound or numerical failure probability.
