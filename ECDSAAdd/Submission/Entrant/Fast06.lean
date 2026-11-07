import ECDSAAdd.Submission.Entrant.MainBase
import ECDSAAdd.Submission.Entrant.Fast00
import ECDSAAdd.Submission.Entrant.Fast01
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ZeroFill
open Arithmetic

def clearFV (a : Nat) (aL aH : Bool) (U V F xlo xhi el eh : Wire)
    (top mid : List (Nat × Wire × Wire)) : Program :=
  [.measureX F [] (compareCorrections aH xhi V eh (correctionWires a top)),
   .measureX V [] (compareCorrections aL xlo U el (correctionWires a mid))]

theorem clearFV_counts (a : Nat) (aL aH : Bool) (U V F xlo xhi el eh : Wire)
    (top mid : List (Nat × Wire × Wire)) :
    toffoliCount (clearFV a aL aH U V F xlo xhi el eh top mid) = 0 ∧
      measurementCount (clearFV a aL aH U V F xlo xhi el eh top mid) = 2 := by
  simp [clearFV, toffoliCount, measurementCount]
theorem clearFV_correct (a : Nat) (aL aH : Bool) (U V F xlo xhi el eh : Wire)
    (top mid : List (Nat × Wire × Wire)) (s : State) (m : List Bool)
    (hhF : xhi ≠ F) (hVF : V ≠ F) (hEF : eh ≠ F)
    (hlV : xlo ≠ V) (hUV : U ≠ V) (heV : el ≠ V)
    (hlF : xlo ≠ F) (hUF : U ≠ F) (heF : el ≠ F)
    (htop : ∀ w ∈ correctionWires a top, w ≠ F)
    (hmidV : ∀ w ∈ correctionWires a mid, w ≠ V)
    (hmidF : ∀ w ∈ correctionWires a mid, w ≠ F)
    (hf : s.basis F = (((s.basis xhi == aH) && s.basis V) ^^
       ECDSAAdd.parityAt s.basis (correctionWires a top) ^^ (s.basis eh && (s.basis xhi && !aH))))
    (hv : s.basis V = (((s.basis xlo == aL) && s.basis U) ^^
       ECDSAAdd.parityAt s.basis (correctionWires a mid) ^^ (s.basis el && (s.basis xlo && !aL)))) :
    run (clearFV a aL aH U V F xlo xhi el eh top mid) m s =
       ⟨s.phase, writeBit (writeBit s.basis F false) V false⟩ := by
  unfold clearFV
  change run ([.measureX F [] (compareCorrections aH xhi V eh (correctionWires a top))] ++
    [.measureX V [] (compareCorrections aL xlo U el (correctionWires a mid))]) m s = _
  rw [run_append]
  rw [eraseCompareAccumulator aH xhi V eh F (correctionWires a top) hhF hVF hEF htop s _ hf]
  have hv' : (writeBit s.basis F false) V =
      ((((writeBit s.basis F false) xlo == aL) && (writeBit s.basis F false) U) ^^
      ECDSAAdd.parityAt (writeBit s.basis F false) (correctionWires a mid) ^^
      ((writeBit s.basis F false) el && ((writeBit s.basis F false) xlo && !aL))) := by
    rw [parityAt_update s.basis F (correctionWires a mid) hmidF]
    simpa [writeBit, Function.update_of_ne hVF, Function.update_of_ne hlF,
      Function.update_of_ne hUF, Function.update_of_ne heF] using hv
  exact eraseCompareAccumulator aL xlo U el V (correctionWires a mid) hlV hUV heV hmidV
    ⟨s.phase, writeBit s.basis F false⟩ _ hv'

end ECDSAAdd.Entrant.ZeroFill
