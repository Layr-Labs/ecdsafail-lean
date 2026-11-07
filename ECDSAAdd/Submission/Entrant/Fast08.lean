import ECDSAAdd.Submission.Entrant.Fast06
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
namespace ECDSAAdd.Entrant.ZeroFill
open Arithmetic

theorem parityAt_updateAny_research (basis : BasisState) (t : Wire) (v : Bool) (ws : List Wire)
    (h : ∀ w ∈ ws, w ≠ t) : ECDSAAdd.parityAt (writeBit basis t v) ws = ECDSAAdd.parityAt basis ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [ECDSAAdd.parityAt]
    rw [show writeBit basis t v w = basis w by simpa [writeBit] using (Function.update_of_ne (h w (by simp)) v basis)]
    rw [ih (fun w hw => h w (by simp [hw]))]

theorem ccx_clearFV_correct (a : Nat) (aL aH : Bool) (U V F xlo xhi el eh g pk : Wire)
    (top mid : List (Nat × Wire × Wire)) (s : State) (m : List Bool)
    (hhF : xhi ≠ F) (hVF : V ≠ F) (hEF : eh ≠ F)
    (hlV : xlo ≠ V) (hUV : U ≠ V) (heV : el ≠ V)
    (hlF : xlo ≠ F) (hUF : U ≠ F) (heF : el ≠ F)
    (hFp : F ≠ pk) (hVp : V ≠ pk) (hUp : U ≠ pk)
    (hxp : xlo ≠ pk) (hXp : xhi ≠ pk) (hep : el ≠ pk) (hEp : eh ≠ pk)
    (htop : ∀ w ∈ correctionWires a top, w ≠ F)
    (hmidV : ∀ w ∈ correctionWires a mid, w ≠ V)
    (hmidF : ∀ w ∈ correctionWires a mid, w ≠ F)
    (htopP : ∀ w ∈ correctionWires a top, w ≠ pk)
    (hmidP : ∀ w ∈ correctionWires a mid, w ≠ pk)
    (hf : s.basis F = (((s.basis xhi == aH) && s.basis V) ^^
       ECDSAAdd.parityAt s.basis (correctionWires a top) ^^ (s.basis eh && (s.basis xhi && !aH))))
    (hv : s.basis V = (((s.basis xlo == aL) && s.basis U) ^^
       ECDSAAdd.parityAt s.basis (correctionWires a mid) ^^ (s.basis el && (s.basis xlo && !aL)))) :
    run ([.CCX g F pk] ++ clearFV a aL aH U V F xlo xhi el eh top mid) m s =
      ⟨s.phase, writeBit (writeBit (writeBit s.basis pk (s.basis pk ^^ (s.basis g && s.basis F))) F false) V false⟩ := by
  let v := s.basis pk ^^ (s.basis g && s.basis F)
  let t : State := ⟨s.phase, writeBit s.basis pk v⟩
  have hf' : t.basis F = (((t.basis xhi == aH) && t.basis V) ^^
       ECDSAAdd.parityAt t.basis (correctionWires a top) ^^ (t.basis eh && (t.basis xhi && !aH))) := by
    dsimp [t]
    rw [parityAt_updateAny_research s.basis pk v (correctionWires a top) htopP]
    simpa [writeBit, Function.update_of_ne hFp, Function.update_of_ne hVp,
      Function.update_of_ne hXp, Function.update_of_ne hEp] using hf
  have hv' : t.basis V = (((t.basis xlo == aL) && t.basis U) ^^
       ECDSAAdd.parityAt t.basis (correctionWires a mid) ^^ (t.basis el && (t.basis xlo && !aL))) := by
    dsimp [t]
    rw [parityAt_updateAny_research s.basis pk v (correctionWires a mid) hmidP]
    simpa [writeBit, Function.update_of_ne hVp, Function.update_of_ne hUp,
      Function.update_of_ne hxp, Function.update_of_ne hep] using hv
  rw [run_cat _ _ rfl]
  change run (clearFV a aL aH U V F xlo xhi el eh top mid) m t = _
  exact clearFV_correct a aL aH U V F xlo xhi el eh top mid t m hhF hVF hEF
    hlV hUV heV hlF hUF heF htop hmidV hmidF hf' hv'
end ECDSAAdd.Entrant.ZeroFill
