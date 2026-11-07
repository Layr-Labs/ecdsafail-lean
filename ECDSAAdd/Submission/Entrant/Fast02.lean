import ECDSAAdd.Submission.Entrant.MainBase
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ZeroFill
open Arithmetic

theorem pre_U_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let st := writeBit s.basis one (!s.basis one)
    (run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis U = accVal a st low := by
  intro st
  have sU : st U = false := by simp [st, writeBit, hoU.symm, hU]
  have sV : st V = false := by simp [st, writeBit, hoV.symm, hV]
  have sF : st F = false := by simp [st, writeBit, hoF.symm, hF]
  have tl : ∀ x ∈ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧ (x.2.1 ≠ F ∧ x.2.2 ≠ F) :=
    fun x hx => hT x (by simp [hx])
  have tm : ∀ x ∈ mid, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧ (x.2.1 ≠ F ∧ x.2.2 ≠ F) :=
    fun x hx => hT x (by simp [hx])
  have tt : ∀ x ∈ top, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧ (x.2.1 ≠ F ∧ x.2.2 ≠ F) :=
    fun x hx => hT x (by simp [hx])
  simp only [pre]
  rw [run_cat _ _ rfl, run_cat _ _ (xorAcc_mc ..), run_cat _ _ (muxAnd_mc ..),
    run_cat _ _ (xorAcc_mc ..), run_cat _ _ (muxAnd_mc ..)]
  have h1 : run [Instr.X one] [] s = ⟨s.phase, st⟩ := rfl
  rw [h1]
  clear_value st
  rw [run_xorAcc a U low (fun x hx => (tl x hx).1)]
  rw [run_muxAnd aL el xlo U V heU hlU hlV hUV heV]
  rw [run_xorAcc a V mid (fun x hx => (tm x hx).2.1)]
  rw [run_muxAnd aH eh xhi V F hEV hhV hhF hVF hEF]
  rw [run_xorAcc a F top (fun x hx => (tt x hx).2.2)]
  have aMU : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b U v) mid = accVal a b mid :=
    fun b v => accVal_write a b U v mid (fun x hx => (tm x hx).1)
  have aMV : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b V v) mid = accVal a b mid :=
    fun b v => accVal_write a b V v mid (fun x hx => (tm x hx).2.1)
  have aTU : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b U v) top = accVal a b top :=
    fun b v => accVal_write a b U v top (fun x hx => (tt x hx).1)
  have aTV : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b V v) top = accVal a b top :=
    fun b v => accVal_write a b V v top (fun x hx => (tt x hx).2.1)
  have aTF : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b F v) top = accVal a b top :=
    fun b v => accVal_write a b F v top (fun x hx => (tt x hx).2.2)
  simp only [xw, aMU, aMV, aTU, aTV, aTF]
  simp only [writeBit, Function.update_self, Function.update_of_ne hVF.symm,
    Function.update_of_ne hUF.symm, Function.update_of_ne hhF, Function.update_of_ne hEF,
    Function.update_of_ne hEV, Function.update_of_ne hEU]
  simp only [Function.update_apply, hhU, hhV, hlU, hlV, heU, heV, hEU, hEV, hEF, hUV.symm, hVF.symm,
    hUF.symm, if_false, if_true, sU, sV, sF, Bool.false_xor, Bool.xor_false]


  simp [hVF, hUV, hUF]


theorem pre_V_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let st := writeBit s.basis one (!s.basis one)
    (run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis V =
      (((st xlo == aL) && accVal a st low) ^^ accVal a st mid ^^ (st el && (st xlo && !aL))) := by
  intro st
  have sU : st U = false := by simp [st, writeBit, hoU.symm, hU]
  have sV : st V = false := by simp [st, writeBit, hoV.symm, hV]
  have sF : st F = false := by simp [st, writeBit, hoF.symm, hF]
  have tl : ∀ x ∈ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧ (x.2.1 ≠ F ∧ x.2.2 ≠ F) :=
    fun x hx => hT x (by simp [hx])
  have tm : ∀ x ∈ mid, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧ (x.2.1 ≠ F ∧ x.2.2 ≠ F) :=
    fun x hx => hT x (by simp [hx])
  have tt : ∀ x ∈ top, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧ (x.2.1 ≠ F ∧ x.2.2 ≠ F) :=
    fun x hx => hT x (by simp [hx])
  simp only [pre]
  rw [run_cat _ _ rfl, run_cat _ _ (xorAcc_mc ..), run_cat _ _ (muxAnd_mc ..),
    run_cat _ _ (xorAcc_mc ..), run_cat _ _ (muxAnd_mc ..)]
  have h1 : run [Instr.X one] [] s = ⟨s.phase, st⟩ := rfl
  rw [h1]
  clear_value st
  rw [run_xorAcc a U low (fun x hx => (tl x hx).1)]
  rw [run_muxAnd aL el xlo U V heU hlU hlV hUV heV]
  rw [run_xorAcc a V mid (fun x hx => (tm x hx).2.1)]
  rw [run_muxAnd aH eh xhi V F hEV hhV hhF hVF hEF]
  rw [run_xorAcc a F top (fun x hx => (tt x hx).2.2)]
  have aMU : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b U v) mid = accVal a b mid :=
    fun b v => accVal_write a b U v mid (fun x hx => (tm x hx).1)
  have aMV : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b V v) mid = accVal a b mid :=
    fun b v => accVal_write a b V v mid (fun x hx => (tm x hx).2.1)
  have aTU : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b U v) top = accVal a b top :=
    fun b v => accVal_write a b U v top (fun x hx => (tt x hx).1)
  have aTV : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b V v) top = accVal a b top :=
    fun b v => accVal_write a b V v top (fun x hx => (tt x hx).2.1)
  have aTF : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b F v) top = accVal a b top :=
    fun b v => accVal_write a b F v top (fun x hx => (tt x hx).2.2)
  simp only [xw, aMU, aMV, aTU, aTV, aTF]
  simp only [writeBit, Function.update_self, Function.update_of_ne hVF.symm,
    Function.update_of_ne hUF.symm, Function.update_of_ne hhF, Function.update_of_ne hEF,
    Function.update_of_ne hEV, Function.update_of_ne hEU]
  simp only [Function.update_apply, hhU, hhV, hlU, hlV, heU, heV, hEU, hEV, hEF, hUV.symm, hVF.symm,
    hUF.symm, if_false, if_true, sU, sV, sF, Bool.false_xor, Bool.xor_false]


  simp [hVF, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]


theorem pre_outside_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) (q : Wire)
    (hqU : q ≠ U) (hqV : q ≠ V) (hqF : q ≠ F)
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let st := writeBit s.basis one (!s.basis one)
    (run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s).basis q = st q := by
  intro st
  have sU : st U = false := by simp [st, writeBit, hoU.symm, hU]
  have sV : st V = false := by simp [st, writeBit, hoV.symm, hV]
  have sF : st F = false := by simp [st, writeBit, hoF.symm, hF]
  have tl : ∀ x ∈ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧ (x.2.1 ≠ F ∧ x.2.2 ≠ F) :=
    fun x hx => hT x (by simp [hx])
  have tm : ∀ x ∈ mid, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧ (x.2.1 ≠ F ∧ x.2.2 ≠ F) :=
    fun x hx => hT x (by simp [hx])
  have tt : ∀ x ∈ top, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧ (x.2.1 ≠ F ∧ x.2.2 ≠ F) :=
    fun x hx => hT x (by simp [hx])
  simp only [pre]
  rw [run_cat _ _ rfl, run_cat _ _ (xorAcc_mc ..), run_cat _ _ (muxAnd_mc ..),
    run_cat _ _ (xorAcc_mc ..), run_cat _ _ (muxAnd_mc ..)]
  have h1 : run [Instr.X one] [] s = ⟨s.phase, st⟩ := rfl
  rw [h1]
  clear_value st
  rw [run_xorAcc a U low (fun x hx => (tl x hx).1)]
  rw [run_muxAnd aL el xlo U V heU hlU hlV hUV heV]
  rw [run_xorAcc a V mid (fun x hx => (tm x hx).2.1)]
  rw [run_muxAnd aH eh xhi V F hEV hhV hhF hVF hEF]
  rw [run_xorAcc a F top (fun x hx => (tt x hx).2.2)]
  have aMU : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b U v) mid = accVal a b mid :=
    fun b v => accVal_write a b U v mid (fun x hx => (tm x hx).1)
  have aMV : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b V v) mid = accVal a b mid :=
    fun b v => accVal_write a b V v mid (fun x hx => (tm x hx).2.1)
  have aTU : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b U v) top = accVal a b top :=
    fun b v => accVal_write a b U v top (fun x hx => (tt x hx).1)
  have aTV : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b V v) top = accVal a b top :=
    fun b v => accVal_write a b V v top (fun x hx => (tt x hx).2.1)
  have aTF : ∀ (b : BasisState) (v : Bool), accVal a (writeBit b F v) top = accVal a b top :=
    fun b v => accVal_write a b F v top (fun x hx => (tt x hx).2.2)
  simp only [xw, aMU, aMV, aTU, aTV, aTF]
  simp only [writeBit, Function.update_self, Function.update_of_ne hVF.symm,
    Function.update_of_ne hUF.symm, Function.update_of_ne hhF, Function.update_of_ne hEF,
    Function.update_of_ne hEV, Function.update_of_ne hEU]
  simp only [Function.update_apply, hhU, hhV, hlU, hlV, heU, heV, hEU, hEV, hEF, hUV.symm, hVF.symm,
    hUF.symm, if_false, if_true, sU, sV, sF, Bool.false_xor, Bool.xor_false]


  simp [hVF, hqU, hqV, hqF]


end ECDSAAdd.Entrant.ZeroFill
