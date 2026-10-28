import ECDSAAdd.Arithmetic.Rotate
import ECDSAAdd.Framework.RecordedSemantics

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- The selected source-SWAP lowering exchanges the two bits and preserves phase. -/
theorem rowMul_swap_lowering (a b : Wire) (hab : a ≠ b) (s : State) (m : List Bool) :
    run (swapBits a b) m s =
      ⟨s.phase, fun q => if q = a then s.basis b else if q = b then s.basis a else s.basis q⟩ := by
  apply congrArg₂ State.mk
  · rfl
  · funext q
    by_cases ha : q = a
    · subst q
      cases h₁ : s.basis a <;> cases h₂ : s.basis b <;>
        simp [writeBit, hab, Ne.symm hab, h₂]
    by_cases hb : q = b
    · subst q
      cases h₁ : s.basis a <;> cases h₂ : s.basis b <;>
        simp [writeBit, hab, Ne.symm hab, h₂]
    · simp [writeBit, ha, hb]

/-- Both conventional three-CX expansions implement the same full-state map. -/
theorem rowMul_swap_directions (a b : Wire) (hab : a ≠ b) (s : State) (m : List Bool) :
    run [.CX a b, .CX b a, .CX a b] m s = run (swapBits a b) m s := by
  change run (swapBits b a) m s = _
  rw [rowMul_swap_lowering b a (Ne.symm hab), rowMul_swap_lowering a b hab]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases ha : q = a <;> by_cases hb : q = b <;> simp_all

/-- Semantic symmetry only: generated CCX operand order is not rewritten. -/
theorem rowMul_ccx_controls (a b t : Wire) (s : State) (m : List Bool) :
    run [.CCX a b t] m s = run [.CCX b a t] m s := by
  simp only [run, Bool.and_comm]

/-- Adjacent same-target CX gates commute when neither control is the target.
Used to relate the older fold presentation; source order is retained. -/
theorem rowMul_cx_same_target (a b t : Wire) (ha : a ≠ t) (hb : b ≠ t)
    (s : State) (m : List Bool) :
    run [.CX a t, .CX b t] m s = run [.CX b t, .CX a t] m s := by
  apply congrArg₂ State.mk
  · rfl
  · funext q
    by_cases hq : q = t
    · subst q
      cases h₁ : s.basis a <;> cases h₂ : s.basis b <;> cases h₃ : s.basis t <;>
        simp [writeBit, ha, hb, h₁, h₂]
    · simp [writeBit, hq]

/-- Consecutive corrections reading the same record act as their ordered list. -/
theorem rowMul_record_corrections (cs : List Correction) (tape : List Bool)
    (ordinal cursor : Nat) (s : State) :
    runWithTape (cs.map (fun c => .phaseFromRecord ordinal [c])) tape cursor s =
      if tape.getD ordinal false then correct cs s else s := by
  induction cs generalizing s with
  | nil => simp [runWithTape, correct]
  | cons c cs ih =>
    simp only [List.map_cons, runWithTape]
    rw [ih]
    split <;> cases c <;> simp_all [correct]

/-- Fuse an HMR and its immediately following corrections, preserving phase
on all tapes including the empty/default-false tape. -/
theorem rowMul_measure_fusion (q : Wire) (cs : List Correction) (tape : List Bool)
    (cursor : Nat) (s : State) :
    runWithTape (.gate (.measureX q [] []) ::
      cs.map (fun c => .phaseFromRecord cursor [c])) tape cursor s =
    runWithTape [.gate (.measureX q [] cs)] tape cursor s := by
  simp only [runWithTape, rowMul_record_corrections, run, measureAndCorrect]
  have h : (tape.drop cursor).headD false = tape.getD cursor false := by
    induction cursor generalizing tape with
    | zero => cases tape <;> rfl
    | succ k ih =>
      cases tape with
      | nil => rfl
      | cons b bs => exact ih bs
  rw [h]
  split <;> simp_all [correct]

end ECDSAAdd.Arithmetic.Paper935
