import ECDSAAdd.Framework.FiniteUnitary
import ECDSAAdd.Submission.Entrant.Fast09
import ECDSAAdd.Submission.Entrant.Fast10
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
namespace ECDSAAdd.Entrant.ZeroFill
open Arithmetic

def fastExtract (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) : Program :=
  pre a aL aH one U V F xlo xhi el eh top mid low ++
    ([.CCX g F pk] ++ clearFV a aL aH U V F xlo xhi el eh top mid ++ finishUOne a one U low)

theorem fastExtract_counts (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) :
    toffoliCount (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) ≤ 3 ∧
    measurementCount (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) = 2 := by
  have hp := pre_counts a aL aH one U V F xlo xhi el eh top mid low
  have hc := clearFV_counts a aL aH U V F xlo xhi el eh top mid
  have hf := finishUOne_counts a one U low
  simp only [fastExtract, toffoliCount_append, measurementCount_append, toffoliCount, measurementCount,
    hc.1, hc.2, hf.1, hf.2] 
  omega
theorem fastExtract_post (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) (g pk : Wire)
    (hFp : F ≠ pk) (hVp : V ≠ pk) (hUp : U ≠ pk)
    (hxp : xlo ≠ pk) (hXp : xhi ≠ pk) (hep : el ≠ pk) (hEp : eh ≠ pk)
    (htopP : ∀ w ∈ correctionWires a top, w ≠ pk)
    (hmidP : ∀ w ∈ correctionWires a mid, w ≠ pk)
    (honeP : one ≠ pk)
    (hlowP : ∀ x ∈ low, x.2.1 ≠ pk ∧ x.2.2 ≠ pk)
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (m : List Bool) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
    let r : State := ⟨t.phase, writeBit (writeBit (writeBit t.basis pk (t.basis pk ^^ (t.basis g && t.basis F))) F false) V false⟩
    run (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) m s =
      ⟨r.phase, writeBit (writeBit r.basis U false) one (!r.basis one)⟩ := by
  let st := writeBit s.basis one (!s.basis one)
  let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
  let r : State := ⟨t.phase, writeBit (writeBit (writeBit t.basis pk (t.basis pk ^^ (t.basis g && t.basis F))) F false) V false⟩
  have out (q : Wire) (qu : q ≠ U) (qv : q ≠ V) (qf : q ≠ F) : t.basis q = st q := by
    exact pre_outside_research a aL aH one U V F xlo xhi el eh top mid low q qu qv qf
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have hu : t.basis U = accVal a st low := by
    exact pre_U_research a aL aH one U V F xlo xhi el eh top mid low
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have hlow : ∀ x ∈ low, x.2.1 ≠ U ∧ x.2.2 ≠ U := by
    intro x hx
    exact (hT x (by simp [hx])).1
  have hacc : accVal a r.basis low = accVal a st low := by
    apply accVal_congr_research
    intro x hx
    have h := hT x (by simp [hx])
    have hp := hlowP x hx
    constructor
    · change writeBit (writeBit (writeBit t.basis pk _) F false) V false x.2.1 = st x.2.1
      rw [show writeBit (writeBit (writeBit t.basis pk _) F false) V false x.2.1 = t.basis x.2.1 by
        simp [writeBit, Function.update_of_ne h.2.1.1, Function.update_of_ne h.2.2.1, Function.update_of_ne hp.1]]
      exact out x.2.1 h.1.1 h.2.1.1 h.2.2.1
    · change writeBit (writeBit (writeBit t.basis pk _) F false) V false x.2.2 = st x.2.2
      rw [show writeBit (writeBit (writeBit t.basis pk _) F false) V false x.2.2 = t.basis x.2.2 by
        simp [writeBit, Function.update_of_ne h.2.1.2, Function.update_of_ne h.2.2.2, Function.update_of_ne hp.2]]
      exact out x.2.2 h.1.2 h.2.1.2 h.2.2.2
  have hrU : r.basis U = accVal a r.basis low := by
    rw [hacc, ←hu]
    simp [r, writeBit, Function.update_of_ne hUV, Function.update_of_ne hUF, Function.update_of_ne hUp]
  have hm : measurementCount (pre a aL aH one U V F xlo xhi el eh top mid low ++
      ([.CCX g F pk] ++ clearFV a aL aH U V F xlo xhi el eh top mid)) = 2 := by
    simp [measurementCount_append, (pre_counts a aL aH one U V F xlo xhi el eh top mid low).2.1,
      (clearFV_counts a aL aH U V F xlo xhi el eh top mid).2, measurementCount]
  unfold fastExtract
  rw [←List.append_assoc, run_append]
  rw [pre_ccx_clearFV_research a aL aH one U V F xlo xhi el eh top mid low g pk
    hFp hVp hUp hxp hXp hep hEp htopP hmidP hUV hUF hVF hlU hlV hlF hhU hhV hhF
    heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s _ hU hV hF]
  exact finishUOne_correct a one U low hoU hlow r _ hrU

theorem fastExtract_semantics (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) (g pk : Wire)
    (hFp : F ≠ pk) (hVp : V ≠ pk) (hUp : U ≠ pk)
    (hxp : xlo ≠ pk) (hXp : xhi ≠ pk) (hep : el ≠ pk) (hEp : eh ≠ pk)
    (htopP : ∀ w ∈ correctionWires a top, w ≠ pk)
    (hmidP : ∀ w ∈ correctionWires a mid, w ≠ pk)
    (honeP : one ≠ pk)
    (hlowP : ∀ x ∈ low, x.2.1 ≠ pk ∧ x.2.2 ≠ pk)
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (m : List Bool) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
    run (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) m s =
      ⟨s.phase, writeBit s.basis pk (s.basis pk ^^ (t.basis g && t.basis F))⟩ := by
  let st := writeBit s.basis one (!s.basis one)
  let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
  let r : State := ⟨t.phase, writeBit (writeBit (writeBit t.basis pk (t.basis pk ^^ (t.basis g && t.basis F))) F false) V false⟩
  have out (q : Wire) (qu : q ≠ U) (qv : q ≠ V) (qf : q ≠ F) : t.basis q = st q := by
    exact pre_outside_research a aL aH one U V F xlo xhi el eh top mid low q qu qv qf
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have hone : t.basis one = !s.basis one := by
    simpa [st, writeBit] using out one hoU hoV hoF
  have hpk : t.basis pk = s.basis pk := by
    simpa [st, writeBit, Function.update_of_ne honeP.symm] using out pk hUp.symm hVp.symm hFp.symm
  have hphase : t.phase = s.phase := by
    exact ECDSAAdd.FiniteUnitary.run_phase _
      (pre_proper a aL aH one U V F xlo xhi el eh top mid low hlV hUV hhF hVF heU hEV hT) s []
  dsimp [t] at hone hpk
  rw [fastExtract_post a aL aH one U V F xlo xhi el eh top mid low g pk
    hFp hVp hUp hxp hXp hep hEp htopP hmidP honeP hlowP hUV hUF hVF hlU hlV hlF hhU hhV hhF
    heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s m hU hV hF]
  apply State.extensionality
  · exact hphase
  · funext q
    by_cases qU : q = U
    · subst q
      simp [r, writeBit, Function.update_apply, hU, hUp, hUV, hUF, hoU, hoU.symm, hUp.symm, honeP, honeP.symm, hoV, hoF, hone]
    · by_cases qV : q = V
      · subst q
        simp [r, writeBit, Function.update_apply, hV, hVp, hUV, hVF, hoV, hoV.symm, hVp.symm, honeP, honeP.symm, hoU, hoF, hone]
      · by_cases qF : q = F
        · subst q
          simp [r, writeBit, Function.update_apply, hF, hFp, hUF, hVF, hoF, hoF.symm, hFp.symm, honeP, honeP.symm, hoU, hoV, hone]
        · by_cases qo : q = one
          · subst q
            simp [r, writeBit, Function.update_apply, hoU, hoV, hoF, honeP, honeP.symm, hUp, hVp, hFp, hone]
          · by_cases qp : q = pk
            · subst q
              simp [r, writeBit, Function.update_apply, hUp, hVp, hFp, hUp.symm, hVp.symm, hFp.symm, honeP, honeP.symm, hpk]
            · have hq := out q qU qV qF
              have hs : t.basis q = s.basis q := by simpa [st, writeBit, Function.update_of_ne qo] using hq
              dsimp [t] at hs
              simp [r, writeBit, Function.update_apply, qU, qV, qF, qo, qp, hs]

theorem fastExtract_equiv (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire)) (g pk : Wire)
    (hFp : F ≠ pk) (hVp : V ≠ pk) (hUp : U ≠ pk)
    (hxp : xlo ≠ pk) (hXp : xhi ≠ pk) (hep : el ≠ pk) (hEp : eh ≠ pk)
    (htopP : ∀ w ∈ correctionWires a top, w ≠ pk)
    (hmidP : ∀ w ∈ correctionWires a mid, w ≠ pk)
    (hPw : pk ∉ wires (pre a aL aH one U V F xlo xhi el eh top mid low))
    (hGP : g ≠ pk)
    (honeP : one ≠ pk)
    (hlowP : ∀ x ∈ low, x.2.1 ≠ pk ∧ x.2.2 ≠ pk)
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (m mOld : List Bool) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    run (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) m s =
      run (pre a aL aH one U V F xlo xhi el eh top mid low ++
        (.CCX g F pk :: (pre a aL aH one U V F xlo xhi el eh top mid low).reverse)) mOld s := by
  rw [fastExtract_semantics a aL aH one U V F xlo xhi el eh top mid low g pk
    hFp hVp hUp hxp hXp hep hEp htopP hmidP honeP hlowP hUV hUF hVF hlU hlV hlF hhU hhV hhF
    heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s m hU hV hF]
  symm
  exact sandwich _ (pre_proper a aL aH one U V F xlo xhi el eh top mid low hlV hUV hhF hVF heU hEV hT)
    g F pk hPw hGP hFp s mOld

theorem proper_gatePhysical_research (p : Program) (hp : ProperProgram p) : Arithmetic.GatePhysical p := by
  intro i hi
  have h := hp i hi
  cases i <;> simp_all [RecordedQuantum.PhysicalInstr, ProperGate]

theorem fastExtract_physical (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hPre : ProperProgram (pre a aL aH one U V F xlo xhi el eh top mid low))
    (hGP : g ≠ pk) (hFP : F ≠ pk)
    (hLow : ∀ x ∈ low, x.2.1 ≠ U ∧ x.2.2 ≠ U) :
    Arithmetic.GatePhysical (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) := by
  have hpre := proper_gatePhysical_research _ hPre
  have hl := proper_gatePhysical_research _ (xorAcc_proper a U low hLow)
  have hcc : Arithmetic.GatePhysical [.CCX g F pk] := by
    simp [Arithmetic.GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hGP, hFP]
  have hclear : Arithmetic.GatePhysical (clearFV a aL aH U V F xlo xhi el eh top mid) := by
    simp [clearFV, Arithmetic.GatePhysical, RecordedQuantum.PhysicalInstr]
  have hfin : Arithmetic.GatePhysical (finishUOne a one U low) := by
    unfold finishUOne
    rw [Arithmetic.gatePhysical_append]
    exact ⟨hl, by simp [Arithmetic.GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate]⟩
  simpa only [fastExtract, Arithmetic.gatePhysical_append] using And.intro hpre (And.intro (And.intro hcc hclear) hfin)

end ECDSAAdd.Entrant.ZeroFill
