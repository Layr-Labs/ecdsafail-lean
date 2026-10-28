# Source row-multiplication prefix equivalence

`HmrRowMulPrefixEquivalence.lean` proves that the first two actual template uses
of both forward calls (`s2ForwardUses` and `s6ForwardUses`) have the same complete
recorded semantics as the existing magnitude-lift and row-fold programs placed
on the ordered source ports. The source data and templates are those checked
against commit `64b5a13aa249f1360846657392e6c66817b26d0f` by the existing generator.

The source instruction stream is unchanged. A small Boolean checker permits
identical instructions, exchange of the two controls of a CCX, and exchange of
two adjacent CX instructions with the same target and controls distinct from
that target. Its soundness theorem preserves the full `State × RecordedContext`,
including phase, tape and cursor. The two concrete checks are evaluated in the
Lean kernel with `decide +kernel`, without raising any limits or using native
execution as a proof.

The public `s2ForwardPrefix_run` and `s6ForwardPrefix_run` theorems hold for every
state and recorded context, including short tapes; no arithmetic success
assumption is needed for this program equivalence. The corresponding measurement
count equalities follow from cursor equality in that same soundness theorem.
`rowMulSourcePrefix` is explicitly `Uses.take 2` instantiated from the actual
port array and measurement start. `rowMulLegacyPrefix` builds the old programs
from the sign, 280 row ports, 256 output ports and 24 ancilla ports in that array.

These theorems do not prove the full row-multiplication scan, any release-zero
obligation, or cancellation of phase debt between calls. `HmrRowMulPrefixLayout.lean` separately binds the existing consumer layouts to
these ordered source ports. The four forward-prefix waiting obligations now
apply these proved results; the remaining 14 waiting proofs are unchanged.
