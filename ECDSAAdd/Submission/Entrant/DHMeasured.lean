import ECDSAAdd.Submission.Entrant.MainPre

/-! Measured first flag clear (port of Meganpark980320 `acfecb68` onto the current wrapper).

The exception wrapper `Edges.finiteProgram` calls `clrDH` twice. The first call, before the
generic block, only uncomputes: each flag already holds exactly the AND the gadget toggles into
it, and ends at 0. Its two flag Toffolis are therefore replaced by X-basis measurements with
their CZ phase corrections (`gadgetM`). The second call is unchanged.

Everything here is additive: `finiteProgramM`/`wrapperM` are new definitions next to the
existing ones, with their own correctness, counts, wires, physicality and slot lemmas. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

section
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

namespace DHGadget

/-- The same gadget when it only uncomputes (`d` and `h` already hold the toggles):
the two target Toffolis become X-basis erasures with their CZ corrections. -/
def gadgetM (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) : Program :=
  [.CCX c f a1, .X g, .CCX a1 g a2, .X g] ++
  ((if enD then
     flipIf (!cx) xk ++ [.CCX a2 xk a3] ++ flipIf (!cx) xk ++
     flipIf (!cy) y0 ++ [.measureX d [] [.CZ a3 y0]] ++ flipIf (!cy) y0 ++
     flipIf (!cx) xk ++ [.measureX a3 [] [.CZ a2 xk]] ++ flipIf (!cx) xk
   else []) ++
  ((if enH then flipIf cx xk ++ [.measureX h [] [.CZ a2 xk]] ++ flipIf cx xk else []) ++
  [.X g, .measureX a2 [] [.CZ a1 g], .X g, .measureX a1 [] [.CZ c f]]))

/-- An X-basis erasure of `t = a ∧ b` with its CZ correction leaves the phase unchanged. -/
theorem measure_erase (t a b : Wire) (x : Bool) (s : State) (ha : a ≠ t) (hb : b ≠ t)
    (h : s.basis t = (s.basis a && s.basis b)) :
    measureAndCorrect t [] [.CZ a b] x s = ⟨s.phase, writeBit s.basis t false⟩ := by
  obtain ⟨ph, bs⟩ := s
  simp only at h
  cases x <;> simp [measureAndCorrect, correct, writeBit, Function.update_apply, ha, hb, h]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 20000000 in
theorem gadgetM_run (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool)
    (hn : [f,xk,y0,c,d,g,h,a1,a2,a3].Nodup) (s : State) (m : List Bool)
    (z1 : s.basis a1 = false) (z2 : s.basis a2 = false) (z3 : s.basis a3 = false)
    (hd : s.basis d = (enD && s.basis c && s.basis f && !s.basis g &&
        (s.basis xk == cx) && (s.basis y0 == cy)))
    (hh : s.basis h = (enH && s.basis c && s.basis f && !s.basis g && (s.basis xk != cx))) :
    run (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) m s = ⟨s.phase, fun q =>
      if q = d then false else if q = h then false else s.basis q⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨⟨n1,n2,n3,n4,n5,n6,n7,n8,n9⟩,⟨m1,m2,m3,m4,m5,m6,m7,m8⟩,⟨k1,k2,k3,k4,k5,k6,k7⟩,
    ⟨l1,l2,l3,l4,l5,l6⟩,⟨p1,p2,p3,p4,p5⟩,⟨q1,q2,q3,q4⟩,⟨r1,r2,r3⟩,⟨t1,t2⟩,t3,-⟩ := hn
  have n1' := Ne.symm n1
  have n2' := Ne.symm n2
  have n3' := Ne.symm n3
  have n4' := Ne.symm n4
  have n5' := Ne.symm n5
  have n6' := Ne.symm n6
  have n7' := Ne.symm n7
  have n8' := Ne.symm n8
  have n9' := Ne.symm n9
  have m1' := Ne.symm m1
  have m2' := Ne.symm m2
  have m3' := Ne.symm m3
  have m4' := Ne.symm m4
  have m5' := Ne.symm m5
  have m6' := Ne.symm m6
  have m7' := Ne.symm m7
  have m8' := Ne.symm m8
  have k1' := Ne.symm k1
  have k2' := Ne.symm k2
  have k3' := Ne.symm k3
  have k4' := Ne.symm k4
  have k5' := Ne.symm k5
  have k6' := Ne.symm k6
  have k7' := Ne.symm k7
  have l1' := Ne.symm l1
  have l2' := Ne.symm l2
  have l3' := Ne.symm l3
  have l4' := Ne.symm l4
  have l5' := Ne.symm l5
  have l6' := Ne.symm l6
  have p1' := Ne.symm p1
  have p2' := Ne.symm p2
  have p3' := Ne.symm p3
  have p4' := Ne.symm p4
  have p5' := Ne.symm p5
  have q1' := Ne.symm q1
  have q2' := Ne.symm q2
  have q3' := Ne.symm q3
  have q4' := Ne.symm q4
  have r1' := Ne.symm r1
  have r2' := Ne.symm r2
  have r3' := Ne.symm r3
  have t1' := Ne.symm t1
  have t2' := Ne.symm t2
  have t3' := Ne.symm t3
  obtain ⟨ph, bs⟩ := s
  simp only at z1 z2 z3 hd hh ⊢
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
  cases hc : bs c <;> cases hf : bs f <;> cases hg : bs g <;> cases hx : bs xk <;> cases hy : bs y0 <;>
  simp only [hc, hf, hg, hx, hy, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
    Bool.not_true, Bool.not_false, beq_self_eq_true, Bool.true_beq, Bool.false_beq, bne_self_eq_false,
    Bool.true_bne, Bool.false_bne] at hd hh <;>
  · simp [gadgetM, flipIf, run, writeBit, Function.update_apply, measure_erase, *]
    funext q
    by_cases e1 : q = d
    · subst e1; simp [Function.update_apply, *]
    by_cases e2 : q = h
    · subst e2; simp [Function.update_apply, *]
    by_cases e3 : q = a1
    · subst e3; simp [Function.update_apply, *]
    by_cases e4 : q = a2
    · subst e4; simp [Function.update_apply, *]
    by_cases e5 : q = a3
    · subst e5; simp [Function.update_apply, *]
    by_cases e6 : q = g
    · subst e6; simp [Function.update_apply, *]
    by_cases e7 : q = xk
    · subst e7; simp [Function.update_apply, *]
    by_cases e8 : q = y0
    · subst e8; simp [Function.update_apply, *]
    simp [Function.update_apply, *]

/-- When the gadget only clears `d` and `h`, the measured variant has the same run. -/
theorem gadgetM_eq (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool)
    (hn : [f,xk,y0,c,d,g,h,a1,a2,a3].Nodup) (s : State) (m : List Bool)
    (z1 : s.basis a1 = false) (z2 : s.basis a2 = false) (z3 : s.basis a3 = false)
    (hd : (s.basis d ^^ (enD && s.basis c && s.basis f && !s.basis g &&
        (s.basis xk == cx) && (s.basis y0 == cy))) = false)
    (hh : (s.basis h ^^ (enH && s.basis c && s.basis f && !s.basis g &&
        (s.basis xk != cx))) = false) :
    run (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) m s =
      run (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) m s := by
  have hd' : s.basis d = (enD && s.basis c && s.basis f && !s.basis g &&
      (s.basis xk == cx) && (s.basis y0 == cy)) := by
    revert hd; cases s.basis d <;> simp
  have hh' : s.basis h = (enH && s.basis c && s.basis f && !s.basis g && (s.basis xk != cx)) := by
    revert hh; cases s.basis h <;> simp
  rw [gadgetM_run c f g d h xk y0 a1 a2 a3 enD enH cx cy hn s m z1 z2 z3 hd' hh',
    gadget_run c f g d h xk y0 a1 a2 a3 enD enH cx cy hn s m z1 z2 z3]
  congr 1
  funext q
  split_ifs
  · exact hd.symm
  · exact hh.symm
  · rfl

theorem gadgetM_wires (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) (q : Wire)
    (hq : q ∈ wires (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy)) :
    q ∈ wires (gadget c f g d h xk y0 a1 a2 a3 enD enH cx cy) := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadgetM, gadget, flipIf, wires, Instr.wires, correctionWires] at hq ⊢ <;> tauto

theorem gadgetM_counts (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool) :
    toffoliCount (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 3 ∧
    measurementCount (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) ≤ 5 := by
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadgetM, flipIf, toffoliCount, measurementCount]

theorem gadgetM_physical (c f g d h xk y0 a1 a2 a3 : Wire) (enD enH cx cy : Bool)
    (hn : [f,xk,y0,c,d,g,h,a1,a2,a3].Nodup) :
    GatePhysical (gadgetM c f g d h xk y0 a1 a2 a3 enD enH cx cy) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  intro i hi
  cases enD <;> cases enH <;> cases cx <;> cases cy <;>
    simp [gadgetM, flipIf] at hi <;> rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp_all [RecordedQuantum.PhysicalInstr, ProperGate, eq_comm]

end DHGadget

/-- `clrDH` where it only clears `D` and `H`: the two flag Toffolis become measured erasures. -/
def clrDHm (L : ControlledPointLayout) (C : Point) (cy : Fp) : Program :=
  DHGadget.gadgetM L.control L.point.finite L.genericSelect L.doubleSelect L.core.equalNegY
    (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1) (L.core.poolWire 2)
    (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C)

section DHFlagM
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw hn in
/-- The measured clear: same triple as `clrDH_flag` when both flags end cleared. -/
theorem clrDHm_flag (C : Point) (cy : Fp) (R : Point) (b D G H : Bool)
    (hD : false = (D ^^ (decide (cy≠-cy) && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R == yBit C))))
    (hH : false = (H ^^ (exceptionBit C && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) != DHClass.cxk C)))) :
    Triple (PointDialogBoundary L R b (dialogFlagState L false D G false false H false))
      (clrDHm L C cy)
      (PointDialogBoundary L R b (dialogFlagState L false false G false false false false)) := by
  intro s m v
  have post := clrDH_flag L hw hn C cy R b D G H false false hD hH s m v
  have nd := dh_nodup L hw hn (DHClass.kx C) (DHClass.kx_lt C)
  have pool3 : ∀ i, i < 3 → s.basis (L.core.poolWire i) = false := by
    intro i hi
    apply (regValue_zero _ _).mp v.clean
    have mem : L.core.poolWire i ∈ L.dialogPool.take 3 := by
      rw [pool_block L hw 3 (by omega)]
      exact List.mem_map.mpr ⟨i, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩
    exact List.mem_of_mem_take mem
  have hrun := DHGadget.gadget_run L.control L.point.finite L.genericSelect L.doubleSelect
    L.core.equalNegY (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1)
    (L.core.poolWire 2) (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C) nd s m
    (pool3 0 (by omega)) (pool3 1 (by omega)) (pool3 2 (by omega))
  have hr' := dialogFlagState_read L hn false false G false false false false
  have outD := (post.2.flags L.doubleSelect (by simp [inPlaceFlags])).trans hr'.2.1
  have outH := (post.2.flags L.core.equalNegY (by simp [inPlaceFlags])).trans hr'.2.2.2.2.2.1
  have dg : L.doubleSelect ≠ L.core.equalNegY := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at nd
    exact nd.2.2.2.2.1.2.1
  change (run (DHGadget.gadget _ _ _ _ _ _ _ _ _ _ _ _ _ _) m s).basis _ = _ at outD outH
  rw [hrun] at outD outH
  simp only [if_true, if_neg (Ne.symm dg)] at outD outH
  have heq := DHGadget.gadgetM_eq L.control L.point.finite L.genericSelect L.doubleSelect
    L.core.equalNegY (L.point.x.getD (DHClass.kx C) 0) (yLow L) (L.core.poolWire 0) (L.core.poolWire 1)
    (L.core.poolWire 2) (decide (cy≠-cy)) (exceptionBit C) (DHClass.cxk C) (yBit C) nd s m
    (pool3 0 (by omega)) (pool3 1 (by omega)) (pool3 2 (by omega)) outD outH
  unfold clrDHm
  rw [heq]
  exact post

end DHFlagM

end ECDSAAdd.Entrant
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Edges
open ECDSAAdd ECDSAAdd.Entrant Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines RecordedQuantum
attribute [local irreducible] run wires

/-- `finiteProgram` with the measured first flag clear. -/
def finiteProgramM (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  inputClass L C cy ++
  genFlagN L ++ clrDHm L C cy ++
  renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) Gen)) ++
  clrDH L C cy ++ mergeFlagsN L ++
  renameProgram (sigP L) (corners2 L C ++ shared L C) ++
  chainErase L.control L.point.finite L.genericSelect

private theorem equal_simpM [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finite_specM (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteProgramM L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  let R1 := if G then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : exceptionBit C = decide (dialogExceptionEnabled C) := by
    simp [exceptionBit,equal_simpM,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simpM]
  have hD : ((b && decide (cy≠-cy)) && pointEqual R C)=D := by
    change (K && pointEqual R C) = D
    rw [hK]; simp only [D,dialogDouble,equal_simpM]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simpM]
  have hH : ((b && exceptionBit C) && pointEqual R (dialogExceptionPoint C))=H := by
    rw [hE]; simp [H,dialogException,dialogExceptionEnabled,equal_simpM]
  have hfin (P : Point) : (b && pointFinite P) = (b ^^ (b && pointEqual P 0)) := by
    rw [pointEqual_zero]; cases b <;> cases pointFinite P <;> rfl
  have hGv : ((((false ^^ (b && pointFinite R)) ^^ D) ^^ I) ^^ H) = G := by
    rw [hfin, hO]; simp only [G, dialogOrdinary, O, D, I, H, Bool.false_xor]
  have hgen := (dialogOrdinary_true b R C hC)
  have hR1fin : (b && pointFinite R1) = (b && pointFinite R) := by
    by_cases hg : G = true
    · obtain ⟨hb, h0, _, hn', _⟩ := hgen.mp hg
      have hs : R + C ≠ 0 := fun e => hn' (eq_neg_of_add_eq_zero_left e)
      have f1 : pointFinite (R+C) = true := by
        have t := pointEqual_zero (R+C)
        have e2 : pointEqual (R+C) 0 = false := by
          cases h : pointEqual (R+C) 0
          · rfl
          · exact absurd ((pointEqual_true_iff _ _).mp h) hs
        rw [e2] at t
        cases h : pointFinite (R+C)
        · rw [h] at t; exact absurd t (by decide)
        · rfl
      have f2 : pointFinite R = true := by
        have t := pointEqual_zero R
        have e2 : pointEqual R 0 = false := by
          cases h : pointEqual R 0
          · rfl
          · exact absurd ((pointEqual_true_iff _ _).mp h) h0
        rw [e2] at t
        cases h : pointFinite R
        · rw [h] at t; exact absurd t (by decide)
        · rfl
      simp only [R1, hg, if_true, f1, f2]
    · simp only [R1, Bool.not_eq_true] at hg ⊢; simp [hg]
  have hR1O : (b && pointEqual R1 0) = O := by
    by_cases hg : G = true
    · obtain ⟨hb, h0, _, hn', _⟩ := hgen.mp hg
      have hs : R + C ≠ 0 := fun e => hn' (eq_neg_of_add_eq_zero_left e)
      have e1 : pointEqual (R+C) 0 = false := by
        cases h : pointEqual (R+C) 0
        · rfl
        · exact absurd ((pointEqual_true_iff _ _).mp h) hs
      have e2 : pointEqual R 0 = false := by
        cases h : pointEqual R 0
        · rfl
        · exact absurd ((pointEqual_true_iff _ _).mp h) h0
      rw [← hO]; simp only [R1, hg, if_true, e1, e2]
    · simp only [R1, Bool.not_eq_true] at hg ⊢; simp [hg, hO]
  have hG1 : (((I ^^ (b && pointFinite R)) ^^ D) ^^ H) = G := by
    rw [← hGv]
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  have hI1 : (((G ^^ (b && pointFinite R1)) ^^ D) ^^ H) = I := by
    rw [hR1fin, ← hGv]
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  have h3 := inputClass_flag L hw hn R C cy b false false false false false false false
  rw [hD,hI,hH,Bool.false_xor,Bool.false_xor,Bool.false_xor] at h3
  have h6 := genFlagN_flag L hn R b false D I false false H false
  rw [hG1] at h6
  have cls := DHClass.classify hc b R
  dsimp only at cls
  have hKC : decide (cy≠-cy) = decide (C≠-C) := by
    apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; exact doubling_enabled_iff hc
  have clrD : false = (D ^^ (decide (cy≠-cy) && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R == yBit C))) := by
    rw [hKC]; simp only [D, G, C]; rw [← cls.1, Bool.xor_self]
  have clrH : false = (H ^^ (exceptionBit C && b && pointFinite R && !G &&
      ((pointX R).testBit (DHClass.kx C) != DHClass.cxk C))) := by
    rw [hE]; simp only [H, G, C]; rw [← cls.2, Bool.xor_self]
  have hf1 := clrDHm_flag L hw hn C cy R b D G H clrD clrH
  have read := dialogFlagState_read L hn false false G false false false false
  have h7 := genericD_ok L hw hn hc Gen hGen R b
    (dialogFlagState L false false G false false false false)
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.1.symm.trans hg)).2) read.2.2.2.2.2.1 read.2.1
  rw [read.2.2.1] at h7
  have resD : D = (false ^^ (decide (cy≠-cy) && b && pointFinite R1 && !G &&
      ((pointX R1).testBit (DHClass.kx C) == DHClass.cxk C) && (yBit R1 == yBit C))) := by
    by_cases hg : G = true
    · rw [hg]; simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_xor]
      simp only [D, C]; rw [cls.1]; simp only [G, C] at hg; simp [hg]
    · have hR1 : R1 = R := by simp only [R1]; rw [if_neg hg]
      rw [hR1, hKC, Bool.false_xor]; simp only [D, G, C]; exact cls.1
  have resH : H = (false ^^ (exceptionBit C && b && pointFinite R1 && !G &&
      ((pointX R1).testBit (DHClass.kx C) != DHClass.cxk C))) := by
    by_cases hg : G = true
    · rw [hg]; simp only [Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_xor]
      simp only [H, C]; rw [cls.2]; simp only [G, C] at hg; simp [hg]
    · have hR1 : R1 = R := by simp only [R1]; rw [if_neg hg]
      rw [hR1, hE, Bool.false_xor]; simp only [H, G, C]; exact cls.2
  have hu := clrDH_flag L hw hn C cy R1 b false G false D H resD resH
  have h9 := genFlagN_flag L hn R1 b false D G false false H false
  rw [hI1] at h9
  have h10a := zeroFlag_flagG L hn R1 b false D I false false H false
  rw [hR1O, Bool.false_xor] at h10a
  have readO := dialogFlagState_read L hn false D I O false H false
  have h8 := corners2_boundary L hw hn R C hC b (dialogFlagState L false D I O false H false)
    readO.2.2.2.1 readO.2.1 readO.2.2.1 readO.2.2.2.2.2.1
  have hf := dialogFlags_output b R C
  have heout : ((b && exceptionBit C) && pointEqual S (-C))=H := by
    rw [hE]
    simpa [H,S,dialogExceptionEnabled,equal_simpM] using hf.2.2.2
  have h10 := shared_flag L hw hn S C b false D I O false H false
  have hdo : (b && pointEqual S (C+C))=D := by
    have hcy : decide (cy≠-cy)=true := by rw [cy_ne_neg hc]
    have hk : K=b := by simp [K,hcy]
    rw [←hk,hK]
    simpa only [equal_simpM] using hf.2.1
  rw [heout,hdo,Bool.xor_self,Bool.xor_self] at h10
  simp only [equal_simpM] at h10
  rw [hf.1,Bool.xor_self] at h10
  have hout := park_triple L hw hn (outStage L C) R1 S b
    (dialogFlagState L false D I false false H false) (dialogFlagState L false false I false false false false)
    (dialogFlagState_read L hn false D I false false H false).2.2.2.1
    (dialogFlagState_read L hn false false I false false false false).2.2.2.1
    (by simpa only [outStage, List.append_assoc] using (h10a.seq h8).seq h10)
  have merge_run (s : State) (m : List Bool) :
      run (mergeFlagsN L ++ renameProgram (sigP L) (corners2 L C ++ shared L C)) m s =
        run (genFlagN L ++ renameProgram (sigP L) (outStage L C)) m s := by
    have shape : genFlagN L ++ renameProgram (sigP L) (outStage L C) =
        (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L)) ++
          renameProgram (sigP L) (corners2 L C ++ shared L C) := by
      simp only [outStage,rename_append,sigP_zeroFlag L hw hn,List.append_assoc]
    rw [shape,run_append,run_take]
    rw [run_append (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L)),run_take]
    simp only [show measurementCount (mergeFlagsN L)=0 from rfl,
      show measurementCount (genFlagN L ++ zeroFlag L.point.finite L.control (parkWire L))=0 from rfl,
      List.drop_zero]
    rw [mergeFlagsN_run_eq L hw hn s m]
  have hmerged : Triple (PointDialogBoundary L R1 b (dialogFlagState L false D G false false H false))
      (mergeFlagsN L ++ renameProgram (sigP L) (corners2 L C ++ shared L C))
      (PointDialogBoundary L S b (dialogFlagState L false false I false false false false)) := by
    intro s m hs
    rw [merge_run]
    exact (h9.seq hout) s m hs
  have hzero : decide (S=0) = !pointFinite S := by
    rw [← equal_simpM]
    exact pointEqual_zero S
  have h12 := chainErase_equalI L hn S b false false (dialogInversePoint b R C)
    false false false false (by rw [← hf.2.2.1, hzero])
  have h := ((((((h3.seq h6).seq hf1).seq h7).seq hu).seq hmerged).seq h12)
  simpa only [finiteProgramM,List.append_assoc,dialogFlagState_zero] using h

theorem finite_countsM (L : ControlledPointLayout) (hw : L.Widths) (Gen : Program) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (finiteProgramM L (.some hc) cy Gen) ≤ 526+toffoliCount Gen ∧
    measurementCount (finiteProgramM L (.some hc) cy Gen) ≤ 521+measurementCount Gen := by
  have inp := inputClass_counts L hw hc
  have out := shared_counts L hw hc
  have zero : toffoliCount (corners2 L (.some hc))=0 ∧ measurementCount (corners2 L (.some hc))=0 := by
    simp only [corners2,toffoliCount_append,measurementCount_append,
      (maskedPointConstant_counts _ _ _).1,(maskedPointConstant_counts _ _ _).2]; decide
  have fo : toffoliCount (clrDH L (.some hc) cy) ≤ 5 ∧ measurementCount (clrDH L (.some hc) cy) ≤ 3 :=
    DHGadget.gadget_counts _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have fm : toffoliCount (clrDHm L (.some hc) cy) ≤ 3 ∧ measurementCount (clrDHm L (.some hc) cy) ≤ 5 :=
    DHGadget.gadgetM_counts _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have z2 : toffoliCount (chainErase L.control L.point.finite L.genericSelect) = 0 ∧
      measurementCount (chainErase L.control L.point.finite L.genericSelect) = 1 := by
    simp [chainErase, toffoliCount, measurementCount]
  have f1 : toffoliCount (genFlagN L) = 1 ∧ measurementCount (genFlagN L) = 0 := by
    simp [genFlagN, toffoliCount, measurementCount]
  have mf : toffoliCount (mergeFlagsN L) = 1 ∧ measurementCount (mergeFlagsN L) = 0 := by
    simp [mergeFlagsN, toffoliCount, measurementCount]
  simp only [finiteProgramM,toffoliCount_append,measurementCount_append,renameProgram_counts,
    out.1,out.2,zero.1,zero.2]
  omega

def wrapperM (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  renameProgram (Wrapper5.U L) (finiteProgramM L C cy (renameProgram (Wrapper5.U L) Gen))

theorem wrapperM_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (wrapperM L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  intro s m hi
  have h := finite_specM L hw hn R hc b (renameProgram (Wrapper5.U L) Gen)
    (Wrapper5.genericOK_relabel L hw hc Gen hGen) s m hi
  unfold wrapperM
  rw [Square5Placement.pool_relabel_state_eq L (Wrapper5.U L) (Wrapper5.U_pool L hw)
    (Wrapper5.U_outside L hw) _ s m hi.clean h.2.clean]
  exact h

theorem wrapperM_counts (L : ControlledPointLayout) (hw : L.Widths) (Gen : Program) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (wrapperM L (.some hc) cy Gen) ≤ 526+toffoliCount Gen ∧
    measurementCount (wrapperM L (.some hc) cy Gen) ≤ 521+measurementCount Gen := by
  simpa only [wrapperM,renameProgram_counts] using
    finite_countsM L hw (renameProgram (Wrapper5.U L) Gen) hc

theorem finiteM_wires (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) :
    wires (finiteProgramM L C cy Gen) ⊆ wires (finiteProgram L C cy Gen) := by
  intro q hq
  have hm : q ∈ wires (clrDHm L C cy) → q ∈ wires (clrDH L C cy) :=
    DHGadget.gadgetM_wires _ _ _ _ _ _ _ _ _ _ _ _ _ _ q
  simp only [finiteProgramM,finiteProgram,wires_append,Finset.mem_union] at hq ⊢
  tauto

theorem wrapperM_wires (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) :
    wires (wrapperM L C cy Gen) ⊆ wires (wrapper L C cy Gen) := by
  intro q hq
  rw [wrapperM,renameProgram_support] at hq
  rw [wrapper,renameProgram_support]
  obtain ⟨old,used,rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨old,finiteM_wires L C cy _ used,rfl⟩

theorem wrapperM_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (hG : wires Gen ⊆ (OB5Support.genericSites L).toFinset) :
    wires (wrapperM L C cy Gen) ⊆ WrapperOB5.support L :=
  (wrapperM_wires L C cy Gen).trans (wrapper_support L hw hn C cy Gen hG)

theorem wrapperM_qubits (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) :
    qubits (wrapperM L C cy Gen) ≤ qubits (wrapper L C cy Gen) :=
  Finset.card_le_card (Finset.union_subset_union (subset_refl _) (wrapperM_wires L C cy Gen))

theorem finite_physicalM (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (hG : GatePhysical Gen) :
    GatePhysical (finiteProgramM L C cy Gen) := by
  have hp := finite_physical L hw hn C cy Gen hG
  have hm : GatePhysical (clrDHm L C cy) :=
    DHGadget.gadgetM_physical _ _ _ _ _ _ _ _ _ _ _ _ _ _ (dh_nodup L hw hn _ (DHClass.kx_lt C))
  simp only [finiteProgram,gatePhysical_append] at hp
  simp only [finiteProgramM,gatePhysical_append]
  tauto

theorem wrapperM_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (hG : GatePhysical Gen) : GatePhysical (wrapperM L C cy Gen) :=
  gatePhysical_rename (Wrapper5.U L) (Wrapper5.U L).injective _
    (finite_physicalM L hw hn C cy _ (gatePhysical_rename (Wrapper5.U L) (Wrapper5.U L).injective Gen hG))

theorem wrapperM_slots (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) :
    gateSlots (wrapperM L C cy Gen) ≤ gateSlots (wrapper L C cy Gen)+2 := by
  have hm : gateSlots (clrDHm L C cy) ≤ gateSlots (clrDH L C cy) + 2 := by
    unfold clrDHm clrDH
    cases decide (cy≠-cy) <;> cases exceptionBit C <;> cases DHClass.cxk C <;> cases yBit C <;>
      simp [DHGadget.gadgetM, DHGadget.gadget, DHGadget.flipIf, gateSlots, Challenge.instructionSlots]
  simp only [wrapperM,wrapper,rename_gateSlots,finiteProgramM,finiteProgram,gateSlots_append]
  omega

/-- `full_spec` for the measured wrapper. -/
theorem full_specM (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen)
    (hG : wires Gen ⊆ (OB5Support.genericSites L).toFinset) :
    {{ L.control=b,L.point=R,L.work=0 }} wrapperM L (.some hc) cy Gen
    {{ L.control=b,L.point=(if b then R+.some hc else R),L.work=0 }} := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have bw : L.inPlaceFlags++L.dialogPool ⊆ L.work := by
    intro q hq
    have h1 := List.count_pos_iff.mpr hq
    have ht := (List.take_sublist 2613 L.core.pool).count_le q
    apply List.count_pos_iff.mp
    simp only [dialogPool,List.count_append] at h1
    simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
      PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
    omega
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (bw hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := wrapperM_spec L hw hn R hc b Gen hGen s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  have hsup := (wrapperM_support L hw hn (.some hc) cy Gen hG).trans (WrapperOB5.support_used L hw)
  have notp : q∉PointAddLayout.pointWires L.point := by
    intro hp
    have hh := List.nodup_iff_count.mp hn q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hp
    simp only [ControlledPointLayout.wires,work,outWork,temporary,ControlledPointLayout.point,extras,selectors,PointAddLayout.wires,
      List.count_append,List.count_cons,List.count_nil] at hh h1 h2
    omega
  have frame : (run (wrapperM L (.some hc) cy Gen) m s).basis q=s.basis q := by
    by_cases hc' : q=L.control
    · subst q; exact ho.control.trans hi.control.symm
    by_cases hf : q∈L.inPlaceFlags
    · exact (ho.flags q hf).trans (hi.flags q hf).symm
    by_cases hw' : q∈L.dialogPool
    · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw'
    apply run_preserves_outside
    apply mt (@hsup q)
    simp [dialogUsedWires,notp,hc',hf,hw']
  rw [frame]
  exact (regValue_zero _ _).mp hz q hq

end ECDSAAdd.Entrant.Edges
end
