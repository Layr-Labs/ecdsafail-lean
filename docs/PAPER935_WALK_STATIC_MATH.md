# Static arithmetic checks and persistent-history framing

`compileAuthorWalk_mathChecks` derives every slot's address-only arithmetic and
post-stage semantic conditions from the actual recursive compiler, initial
geometry and the already checked public budgets. `authorWalk_staticMath`
packages this with unconditional compilation and the 533-slot length. The local
proofs cover routed views, counter and metadata separation, coefficient tags,
retirement addresses and persistent post-stage registers.

`SlotFront.Compiled.intermediates_fit` binds the actual padded layout to the
public pair-max-plus-one widths. Incoming row fit therefore supplies all three
intermediate arithmetic bounds; these are not additional probabilistic events.
`compileCheckedPublicSlot_static_run` removes the separate address and
intermediate-fit premises from the public-slot correctness interface. It still
requires the actual initial state to encode the mathematical rows and metadata,
allocator readiness, the mathematical invariant and exit/counter fit conditions.

The framing results are stronger than a successful-input statement.
`planWindowRows_external` and `compileBankResize_external` preserve every
pre-owned bit outside the input rows, keep it allocated and separate from the
output rows. `RoutedBankLayout.program_support` bounds the actual routed program
by its five controls and row sites. `SlotFront.Compiled.external_frame` and
`compilePublicSlot_external` use these facts and the fresh scratch allocation to
preserve every pre-owned bit outside input rows and metadata on arbitrary states
and measurement tapes. In particular, arithmetic cannot silently change the
persistent history record. Zero states are used only to extract static allocator
facts; the resulting framing statements quantify over arbitrary states.

`pinWalk_inv`, `pinWalk_frozen_zero` and `pinWalk_offset_inputs` establish the
mathematical control-model invariant, frozen-zero implication and both offset
premises. They do not assume trajectory success.

This change does not establish the full compiled forward state/history-value
induction, the inverse endpoint, actual reverse allocation, whole point-addition
935-wire peak or a numerical failure probability. The new public theorems enter
the unchanged exact axiom audit; no verification limits or allowed axioms change.
