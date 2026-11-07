import ECDSAAdd.Submission.Entrant.MainBase
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ZeroFill
open ECDSAAdd

def correctionWires (a : Nat) : List (Nat × Wire × Wire) → List Wire
  | [] => []
  | (i,p,c)::rest => (if a.testBit i then [] else [p,c]) ++ correctionWires a rest

def parityAt (basis : BasisState) : List Wire → Bool
  | [] => false
  | w::ws => basis w ^^ parityAt basis ws

theorem correctionWires_parity (a : Nat) (basis : BasisState) (ts : List (Nat × Wire × Wire)) :
    parityAt basis (correctionWires a ts) = accVal a basis ts := by
  induction ts with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨i,p,c⟩ := v
    cases h : a.testBit i <;> simp [correctionWires, parityAt, accVal, h, ih, Bool.xor_assoc]
theorem accVal_congr_research (a : Nat) (s t : BasisState) (ts : List (Nat × Wire × Wire))
    (h : ∀ x ∈ ts, s x.2.1 = t x.2.1 ∧ s x.2.2 = t x.2.2) :
    accVal a s ts = accVal a t ts := by
  induction ts with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨i,p,c⟩ := x
    have hp := h (i,p,c) (by simp)
    have hr : ∀ x ∈ xs, s x.2.1 = t x.2.1 ∧ s x.2.2 = t x.2.2 := by
      intro x hx
      exact h x (by simp [hx])
    simp only [accVal]
    rw [hp.1, hp.2, ih hr]

end ECDSAAdd.Entrant.ZeroFill
