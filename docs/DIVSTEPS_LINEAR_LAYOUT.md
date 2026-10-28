# Concrete allocation for the 590-slot shared-swap walk

`LinearLayout.lean` supplies an executable allocator and a concrete recorded
program, `numericDivsteps590 cursor`. The earlier 4,337-wire support theorem
required a caller-supplied valid layout with suitable capacities; those layout
hypotheses are now discharged by an explicit construction.

## Construction

`linearRow base width` places a signed row at consecutive addresses, with
explicit low and sign bits. `linearHistory base count` allocates successive
activity/parity/swap triples. `linearLayout n v k m c slots` places the integer,
coefficient and counter data first, then shared mask/carry pools, detection
scratch, two controls, and the history triples.

`linearLayout_used` proves that the complete old allocation is exactly a
consecutive range. Its duplicate-free property supplies `linearLayout_valid`
for widths at least two and the stated shared-pool capacity bounds. These
are symbolic proofs, rather than evaluation of a several-thousand-entry
uniqueness test.

`numericLayout590` instantiates widths 258/592/11, mask 592, carry 591, and 590
future slots. Its validity, widths, capacities, empty past, and original
allocation range `[0,4927)` are proved without caller premises. Applying the
shared-swap schedule retains a duplicate-free allocation of exactly 4,337
addresses. Unused future swap labels are omitted; the remaining labels have
gaps within the old range. There is no contiguous 4,337-label renumbering in
this change, and 4,337 is an upper bound on the program's actual support, not
an exact support-cardinality claim.

## Actual program contracts

For `numericDivsteps590 cursor`:

- `numericDivsteps590_correct` proves complete state restoration for every
  odd nonnegative p below 2^256, every 0≤x≤p, arbitrary incoming phase, tape,
  and cursor, assuming the explicit initial encoding and clean retained
  controls/workspace (`numericLayout590.SharedReady`).
- `numericDivsteps590_counts` proves 5,023,850 Toffolis and 3,321,110 measurements.
- `numericDivsteps590_support` and `numericDivsteps590_qubits` prove support
  containment and the 4,337 upper bound for that same recorded program.
- `numericLayout590_wellFormed slots cursor` supplies well-formed absolute
  measurement references for this concrete layout, including slots=590.

The state-encoding precondition remains explicit; this is not a state
preparation circuit. The schedule is a forward walk followed by its inverse.
It does not assert endpoint g=0, a modular division output, reverse scale
removal, parity/activity-history compression, a 2,613-wire construction, or
point-addition integration. The parent checklist items remain open.
