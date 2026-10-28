import ECDSAAdd.Arithmetic.RecordedRailApplySignedAlgebra

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApplySigned

def preparedBits (a : List Wire) (aTop bTop tau : Wire) (bits : BasisState) : BasisState :=
  fun q => if q=tau then signValue aTop bTop tau bits
    else if q∈a then bits q ^^ signValue aTop bTop tau bits else bits q

theorem prepare_state (a : List Wire) (aTop bTop tau : Wire)
    (nd : a.Nodup) (ht : tau∉a) (hat : aTop≠tau) (hbt : bTop≠tau)
    (s : State) (m : List Bool) (k : Nat) :
    runWithTape (prepare a aTop bTop tau) m k s=⟨s.phase,preparedBits a aTop bTop tau s.basis⟩ := by
  rw [prepare,runWithTape_embedRecorded,run_append,run_take]
  simp only [topPre_measurements,List.drop_zero]
  rw [(top_states aTop bTop tau hat hbt _ _).1,mask_state a tau nd ht]
  apply State.extensionality
  · rfl
  · funext q
    by_cases hq : q=tau <;> by_cases ha : q∈a <;>
      simp_all [preparedBits,writeBit,Function.update]

/-- Source preparation chooses subtraction exactly when the operand sign bits
agree. The tau input is a real freshly allocated zero wire. -/
theorem prepared_sign (aTop bTop tau : Wire) (bits : BasisState) (zero : bits tau=false) :
    signValue aTop bTop tau bits=(!(bits aTop ^^ bits bTop)) := by
  simp [signValue,zero]

theorem prepared_value (a : List Wire) (aTop bTop tau : Wire) (bits : BasisState)
    (away : tau∉a) :
    regValue a (preparedBits a aTop bTop tau bits)=
      if signValue aTop bTop tau bits then 2^a.length-1-regValue a bits else regValue a bits := by
  cases hs : signValue aTop bTop tau bits with
  | false =>
    simp only [hs,Bool.false_eq_true,if_false]
    apply regValue_congr
    intro q hq
    have hqt : q≠tau := by intro he; exact away (he ▸ hq)
    simp [preparedBits,hqt,hq,hs]
  | true =>
    simp only [hs,if_true]
    rw [←regValue_complement a bits]
    apply regValue_congr
    intro q hq
    have hqt : q≠tau := by intro he; exact away (he ▸ hq)
    simp [preparedBits,hqt,hq,hs]

/-- After the word addition, the donor unmask/post gates restore A and retain
S = original B_top XOR updated B_top. S is coherent and is not freed here. -/
theorem restore_after_word (a : List Wire) (aTop bTop tau : Wire)
    (nd : a.Nodup) (ht : tau∉a) (haTop : aTop∈a) (bt : bTop∉a) (hbt : bTop≠tau)
    (original : BasisState) (s : State) (zero : original tau=false)
    (source : ∀q∈a,s.basis q=(original q ^^ signValue aTop bTop tau original))
    (carry : s.basis tau=signValue aTop bTop tau original)
    (m : List Bool) (k : Nat) :
    let out := runWithTape (restore a aTop bTop tau) m k s
    out.phase=s.phase ∧ (∀q∈a,out.basis q=original q) ∧
    out.basis tau=(original bTop ^^ s.basis bTop) ∧
    (∀q,q∉a → q≠tau → out.basis q=s.basis q) := by
  have hat : aTop≠tau := by intro he; exact ht (he ▸ haTop)
  have hta := Ne.symm hat
  have htb := Ne.symm hbt
  rw [restore,runWithTape_embedRecorded,run_append,run_take]
  simp only [mask_measurements,List.drop_zero]
  rw [mask_state a tau nd ht,(top_states aTop bTop tau hat hbt _ _).2]
  dsimp only
  refine ⟨rfl,?_,?_,?_⟩
  · intro q hq
    have hqt : q≠tau := by intro he; exact ht (he ▸ hq)
    have sourceq := source q hq
    simp only [writeBit,Function.update_of_ne hqt,if_pos hq,sourceq,carry]
    cases hs : signValue aTop bTop tau original <;> cases hv : original q <;> simp
  · have sourcetop := source aTop haTop
    cases ha : original aTop <;> cases hb : original bTop <;> cases hn : s.basis bTop <;>
      simp_all [signValue,writeBit,Function.update]
  · intro q hq hqt
    simp [writeBit,Function.update,hq,hqt]

end ECDSAAdd.Arithmetic.RecordedRailApplySigned
#print axioms ECDSAAdd.Arithmetic.RecordedRailApplySigned.prepare_state
#print axioms ECDSAAdd.Arithmetic.RecordedRailApplySigned.restore_after_word
