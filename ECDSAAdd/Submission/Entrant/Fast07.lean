import ECDSAAdd.Submission.Entrant.Fast05
import ECDSAAdd.Submission.Entrant.Fast06
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
namespace ECDSAAdd.Entrant.ZeroFill
open Arithmetic

theorem correctionWires_off_research (a : Nat) (ts : List (Nat × Wire × Wire)) (q : Wire)
    (h : ∀ x ∈ ts, x.2.1 ≠ q ∧ x.2.2 ≠ q) :
    ∀ w ∈ correctionWires a ts, w ≠ q := by
  induction ts with
  | nil => simp [correctionWires]
  | cons x xs ih =>
    obtain ⟨i,p,c⟩ := x
    have hp := h (i,p,c) (by simp)
    have hr : ∀ x ∈ xs, x.2.1 ≠ q ∧ x.2.2 ≠ q := by
      intro x hx; exact h x (by simp [hx])
    intro w hw
    cases hb : a.testBit i
    · simp [correctionWires, hb] at hw
      rcases hw with rfl | rfl | hw
      · exact hp.1
      · exact hp.2
      · exact ih hr w hw
    · simp [correctionWires, hb] at hw
      exact ih hr w hw

theorem pre_then_clearFV_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (m : List Bool) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
    run (pre a aL aH one U V F xlo xhi el eh top mid low ++
       clearFV a aL aH U V F xlo xhi el eh top mid) m s =
       ⟨t.phase, writeBit (writeBit t.basis F false) V false⟩ := by
  let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
  have inv := pre_invariants_research a aL aH one U V F xlo xhi el eh top mid low
    hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have ht : ∀ w ∈ correctionWires a top, w ≠ F := by
    apply correctionWires_off_research
    intro x hx
    exact (hT x (by simp [hx])).2.2
  have hmv : ∀ w ∈ correctionWires a mid, w ≠ V := by
    apply correctionWires_off_research
    intro x hx
    exact (hT x (by simp [hx])).2.1
  have hmf : ∀ w ∈ correctionWires a mid, w ≠ F := by
    apply correctionWires_off_research
    intro x hx
    exact (hT x (by simp [hx])).2.2
  rw [run_cat _ _ (pre_counts a aL aH one U V F xlo xhi el eh top mid low).2.1]
  have eqParity (b : BasisState) (ws : List Wire) : parityAt b ws = ECDSAAdd.parityAt b ws := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simp [parityAt, ECDSAAdd.parityAt, ih]
  have invF : t.basis F = (((t.basis xhi == aH) && t.basis V) ^^ ECDSAAdd.parityAt t.basis (correctionWires a top) ^^ (t.basis eh && (t.basis xhi && !aH))) := by
    simpa only [eqParity] using inv.1
  have invV : t.basis V = (((t.basis xlo == aL) && t.basis U) ^^ ECDSAAdd.parityAt t.basis (correctionWires a mid) ^^ (t.basis el && (t.basis xlo && !aL))) := by
    simpa only [eqParity] using inv.2
  exact clearFV_correct a aL aH U V F xlo xhi el eh top mid t m
    hhF hVF hEF hlV hUV heV hlF hUF heF ht hmv hmf invF invV

end ECDSAAdd.Entrant.ZeroFill
