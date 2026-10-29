import ECDSAAdd.Submission.Entrant.EKFree

/-! The generic flag wire doubles as the infinity flag.

The generic flag is `b ∧ finite ⊕ D ⊕ I ⊕ H` (the four corner cases are
mutually exclusive and finite points are exactly the non-infinity points).
The generic-branch block keeps the finite flag of the point, so the same
formula clears the generic flag right after the block.  The infinity flag is
only needed by the corners and the output tests; it is computed into the then
idle generic wire just before the corners.  The separate infinity-select wire
is no longer used. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

/-- `generic ^= (b ∧ finite) ⊕ D ⊕ I ⊕ H`. -/
def genericFlag2 (L : ControlledPointLayout) : Program :=
  [.CCX L.control L.point.finite L.core.generic, .CX L.doubleSelect L.core.generic,
   .CX L.genericSelect L.core.generic, .CX L.core.equalNegY L.core.generic]

/-- The Skywalk corner writes with the infinity corner controlled by the generic wire. -/
def corners2 (L : ControlledPointLayout) (C : Point) : Program :=
  maskedPointConstant L.core.generic L.point C ++
  maskedPointConstant L.doubleSelect L.point C ++
  maskedPointConstant L.doubleSelect L.point (C+C) ++
  maskedPointConstant L.genericSelect L.point (-C) ++
  maskedPointConstant L.core.equalNegY L.point (dialogExceptionPoint C) ++
  maskedPointConstant L.core.equalNegY L.point (-C)

def finiteProgramFG (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  gatedShort L (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C) ++
  genericFlag2 L ++ Gen ++ genericFlag2 L ++
  zeroFlag L.point.finite L.control L.core.generic ++
  corners2 L C ++
  pairEqual L L.core.generic L.core.equalNegY true (exceptionBit C) C (-C) ++
  gatedShort L (decide (cy≠-cy)) L.doubleSelect (C+C) ++
  chainErase L.control L.point.finite L.genericSelect

section Lemmas
/-- Clearing a flag known to equal `control ∧ ¬finite` by measurement. -/
theorem chainErase_equalI (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (R : Point) (b O D I G E H K : Bool)
    (hI : I = (b && !pointFinite R)) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (chainErase L.control L.point.finite L.genericSelect)
      (PointDialogBoundary L R b (dialogFlagState L O D false G E H K)) := by
  have sep0 := dialogFlag_separation (L:=L) hn
  have hr := dialogFlagState_read L hn O D I G E H K
  have ht : L.genericSelect ∈ L.inPlaceFlags := by simp [inPlaceFlags]
  have hct : L.control ≠ L.genericSelect := fun h => (List.nodup_cons.mp sep0).1 (h ▸ ht)
  have hnd := L.dialogPointZero_nodup hn L.control L.genericSelect hct (Or.inl rfl) ht
  simp only [PointAddLayout.pointWires,List.cons_append,List.nodup_cons,List.mem_cons,
    List.mem_append,not_or] at hnd
  have hcf : L.control ≠ L.point.finite := hnd.1.2.1
  have hft : L.point.finite ≠ L.genericSelect := fun h => hnd.2.1.1 h.symm
  intro s m v
  have hg : s.basis L.genericSelect = I := (v.flags _ ht).trans hr.2.2.1
  have hb : s.basis L.control = b := v.control
  have hfn : s.basis L.point.finite = pointFinite R := ((point_holds _ _ _).mp v.point).1
  have hq : s.basis L.genericSelect = (s.basis L.control && !s.basis L.point.finite) := by
    rw [hg,hb,hfn,hI]
  have hh := chainErase_run L.control L.point.finite L.genericSelect hcf hft hct s m hq
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hqflag
    rw [hh]
    by_cases hqt : q = L.genericSelect
    · subst q
      simp [writeBit, (dialogFlagState_read L hn O D false G E H K).2.2.1]
    · simp only [writeBit,Function.update_apply,hqt,if_false]
      rw [v.flags q hqflag]
      have hu := (dialogFlagState_update L hn O D I G E H K false).2.2.1 q hqflag
      simpa only [writeBit,Function.update_apply,hqt,if_false] using hu
  · intro q hqflag
    rw [hh]
    have hqt : q ≠ L.genericSelect := fun h => hqflag (h ▸ ht)
    simp [writeBit,hqt]

variable (L : ControlledPointLayout)

theorem flags_distinct (hn : L.wires.Nodup) :
    L.control ≠ L.core.generic ∧ L.point.finite ≠ L.core.generic ∧ L.doubleSelect ≠ L.core.generic ∧
    L.genericSelect ≠ L.core.generic ∧ L.core.equalNegY ≠ L.core.generic ∧ L.control ≠ L.point.finite := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hfin : L.point.finite ∉ L.control :: L.inPlaceFlags := by
    have hh := List.nodup_iff_count_le_one.mp (L.dialogUsed_nodup hn) L.point.finite
    have hp : 1 ≤ (PointAddLayout.pointWires L.point).count L.point.finite :=
      List.count_pos_iff.mpr (by simp [PointAddLayout.pointWires])
    simp only [dialogUsedWires, List.count_append] at hh
    have hc : (L.control :: L.inPlaceFlags).count L.point.finite = 0 := by
      show ([L.control] ++ L.inPlaceFlags).count _ = 0
      rw [List.count_append]; omega
    exact List.count_eq_zero.mp hc
  simp only [inPlaceFlags, List.mem_cons, not_or] at hfin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> tauto

theorem genericFlag2_run (hn : L.wires.Nodup) (s : State) (m : List Bool) :
    run (genericFlag2 L) m s = ⟨s.phase, writeBit s.basis L.core.generic
      ((((s.basis L.core.generic ^^ (s.basis L.control && s.basis L.point.finite)) ^^
        s.basis L.doubleSelect) ^^ s.basis L.genericSelect) ^^ s.basis L.core.equalNegY)⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := flags_distinct L hn
  simp only [genericFlag2, run]
  congr 1
  funext q
  by_cases hq : q = L.core.generic
  · subst hq; simp [writeBit, h1, h2, h3, h4, h5]
  · simp [writeBit, hq]

variable (hw : L.Widths) (hn : L.wires.Nodup)
include hn

theorem genericFlag2_flag (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K)) (genericFlag2 L)
      (PointDialogBoundary L R b (dialogFlagState L O D I
        ((((G ^^ (b && pointFinite R)) ^^ D) ^^ I) ^^ H) E H K)) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  intro s m v
  have hh := genericFlag2_run L hn s m
  have hfin : s.basis L.point.finite = pointFinite R := ((point_holds _ _ _).mp v.point).1
  have rd (q : Wire) (hq : q ∈ L.inPlaceFlags) : s.basis q = dialogFlagState L O D I G E H K q := v.flags q hq
  have eG := rd L.core.generic (by simp [inPlaceFlags])
  have eD := rd L.doubleSelect (by simp [inPlaceFlags])
  have eI := rd L.genericSelect (by simp [inPlaceFlags])
  have eH := rd L.core.equalNegY (by simp [inPlaceFlags])
  rw [hr.2.2.2.1] at eG; rw [hr.2.1] at eD; rw [hr.2.2.1] at eI; rw [hr.2.2.2.2.2.1] at eH
  rw [eG, eD, eI, eH, hfin, v.control] at hh
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    have u := (dialogFlagState_update L hn O D I G E H K
      ((((G ^^ (b && pointFinite R)) ^^ D) ^^ I) ^^ H)).2.2.2.1 q hq
    rw [← u]
    by_cases he : q = L.core.generic
    · subst he; simp [writeBit]
    · simp [writeBit, he, rd q hq]
  · intro q hq
    rw [hh]
    have hqt : q ≠ L.core.generic := fun he => hq (he ▸ by simp [inPlaceFlags])
    simp [writeBit, hqt]

theorem zeroFlag_flagG (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (zeroFlag L.point.finite L.control L.core.generic)
      (PointDialogBoundary L R b (dialogFlagState L O D I (G ^^ (b && pointEqual R 0)) E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := zeroFlag_boundary L hn R b (dialogFlagState L O D I G E H K) L.control L.core.generic
    (Or.inl rfl) (by simp [inPlaceFlags]) (by tauto) b (by simp)
  simp only [hr.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.1)

include hw

theorem pairFlag_outputG (S C : Point) (en : Bool) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L S b (dialogFlagState L O D I G E H K))
      (pairEqual L L.core.generic L.core.equalNegY true en C (-C))
      (PointDialogBoundary L S b
        (dialogFlagState L O D I (G ^^ (b && pointEqual S C)) E (H ^^ ((b && en) && pointEqual S (-C))) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn S C b (dialogFlagState L O D I G E H K) L.core.generic L.core.equalNegY
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    true en b (b && en) (by simp) rfl
  simp only [hr.2.2.2.1, hr.2.2.2.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (G ^^ (b && pointEqual S C))).2.2.2.1
  have u2 := (dialogFlagState_update L hn O D I (G ^^ (b && pointEqual S C)) E H K
    (H ^^ ((b && en) && pointEqual S (-C)))).2.2.2.2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

theorem corners2_effect (C : Point) (s : State) (m : List Bool) :
    PointEffect L.point
      ((((((s.basis L.core.generic && pointFinite C) ^^ (s.basis L.doubleSelect && pointFinite C)) ^^
        (s.basis L.doubleSelect && pointFinite (C+C))) ^^ (s.basis L.genericSelect && pointFinite (-C))) ^^
        (s.basis L.core.equalNegY && pointFinite (dialogExceptionPoint C))) ^^
        (s.basis L.core.equalNegY && pointFinite (-C)))
      ((((((if s.basis L.core.generic then pointX C else 0) ^^^ (if s.basis L.doubleSelect then pointX C else 0)) ^^^
        (if s.basis L.doubleSelect then pointX (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointX (-C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointX (dialogExceptionPoint C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointX (-C) else 0))
      ((((((if s.basis L.core.generic then pointY C else 0) ^^^ (if s.basis L.doubleSelect then pointY C else 0)) ^^^
        (if s.basis L.doubleSelect then pointY (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointY (-C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointY (dialogExceptionPoint C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointY (-C) else 0))
      s (run (corners2 L C) m s) := by
  have hr : (PointAddLayout.pointWires L.point).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have hh := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    simp only [List.count_append] at hh
    omega
  have away (q : Wire) (hq : q∈L.inPlaceFlags) : q∉PointAddLayout.pointWires L.point := by
    intro hp
    have hh := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hp
    simp only [List.count_append] at hh
    omega
  have ho := away L.core.generic (by simp [inPlaceFlags])
  have hd := away L.doubleSelect (by simp [inPlaceFlags])
  have hi := away L.genericSelect (by simp [inPlaceFlags])
  have hh' := away L.core.equalNegY (by simp [inPlaceFlags])
  let u := run (maskedPointConstant L.core.generic L.point C) m s
  have e0 := maskedPointConstant_correct _ _ C hr ho hw.inputX hw.inputY s m
  have ud : u.basis L.doubleSelect=s.basis L.doubleSelect := e0.outside _ hd
  let v := run (maskedPointConstant L.doubleSelect L.point C) m u
  have e1 := maskedPointConstant_correct _ _ C hr hd hw.inputX hw.inputY u m
  have vd : v.basis L.doubleSelect=s.basis L.doubleSelect := (e0.trans e1).outside _ hd
  let w := run (maskedPointConstant L.doubleSelect L.point (C+C)) m v
  have e2 := maskedPointConstant_correct _ _ (C+C) hr hd hw.inputX hw.inputY v m
  have wi : w.basis L.genericSelect=s.basis L.genericSelect := ((e0.trans e1).trans e2).outside _ hi
  let x := run (maskedPointConstant L.genericSelect L.point (-C)) m w
  have e3 := maskedPointConstant_correct _ _ (-C) hr hi hw.inputX hw.inputY w m
  have xh : x.basis L.core.equalNegY=s.basis L.core.equalNegY := (((e0.trans e1).trans e2).trans e3).outside _ hh'
  let y := run (maskedPointConstant L.core.equalNegY L.point (dialogExceptionPoint C)) m x
  have e4 := maskedPointConstant_correct _ _ (dialogExceptionPoint C) hr hh' hw.inputX hw.inputY x m
  have yh : y.basis L.core.equalNegY=s.basis L.core.equalNegY :=
    ((((e0.trans e1).trans e2).trans e3).trans e4).outside _ hh'
  have e5 := maskedPointConstant_correct _ _ (-C) hr hh' hw.inputX hw.inputY y m
  have he := ((((e0.trans e1).trans e2).trans e3).trans e4).trans e5
  rw [corners2,run_append,run_take,run_append,run_take,run_append,run_take,run_append,run_take,
    run_append,run_take]
  simp only [measurementCount_append,(maskedPointConstant_counts _ _ _).2,Nat.zero_add,List.drop_zero]
  simpa only [ud,vd,wi,xh,yh] using he

theorem corners2_boundary [DecidableEq Point] (R C : Point) (hc : C≠0) (b : Bool) (f : BasisState)
    (ho : f L.core.generic=dialogInfinity b R)
    (hd : f L.doubleSelect=dialogDouble b R C)
    (hi : f L.genericSelect=dialogInversePoint b R C)
    (hh : f L.core.equalNegY=dialogException b R C) :
    Triple (PointDialogBoundary L (if dialogOrdinary b R C then R+C else R) b f)
      (corners2 L C) (PointDialogBoundary L (if b then R+C else R) b f) := by
  intro s m v
  have he := corners2_effect L hw hn C s m
  have vo := (v.flags _ (by simp [inPlaceFlags])).trans ho
  have vd := (v.flags _ (by simp [inPlaceFlags])).trans hd
  have vi := (v.flags _ (by simp [inPlaceFlags])).trans hi
  have vh := (v.flags _ (by simp [inPlaceFlags])).trans hh
  have hp := (point_holds _ _ _).mp v.point
  refine ⟨he.phase,v.withPoint hn ((point_holds _ _ _).mpr ⟨?_,?_,?_⟩) he.outside⟩
  · rw [he.finite,hp.1,vo,vd,vi,vh]
    have h := dialogCorners_bool b R C hc pointFinite (by rfl)
    have bool_if (a b : Bool) : (if a then b else false)=(a && b) := by cases a <;> rfl
    simpa only [bool_if,Bool.xor_assoc] using h
  · rw [he.x,hp.2.1,vo,vd,vi,vh]
    simpa only [Nat.xor_assoc] using dialogCorners_nat b R C hc pointX (by rfl)
  · rw [he.y,hp.2.2,vo,vd,vi,vh]
    simpa only [Nat.xor_assoc] using dialogCorners_nat b R C hc pointY (by rfl)

end Lemmas

end ECDSAAdd.Entrant

namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

section SpecFG
attribute [local irreducible] run wires shortEqual pairEqual gatedShort genericFlag2 corners2

private theorem equal_simpG [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finiteProgramFG_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteProgramFG L (.some hc) cy Gen)
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
    simp [exceptionBit,equal_simpG,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simpG]
  have hD : ((b && decide (cy≠-cy)) && pointEqual R C)=D := by
    change (K && pointEqual R C) = D
    rw [hK]; simp only [D,dialogDouble,equal_simpG]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simpG]
  have hH : ((b && exceptionBit C) && pointEqual R (dialogExceptionPoint C))=H := by
    rw [hE]; simp [H,dialogException,dialogExceptionEnabled,equal_simpG]
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
  have h3 := pairFlag_inputE L hw hn R C cy b false false false false false false false
  rw [hD,hI,Bool.false_xor,Bool.false_xor] at h3
  have h5 := gatedFlag_H L hw hn R (dialogExceptionPoint C) (exceptionBit C) b false D I false false false false
  rw [hH,Bool.false_xor] at h5
  have h6 := genericFlag2_flag L hn R b false D I false false H false
  rw [hGv] at h6
  have read := dialogFlagState_read L hn false D I G false H false
  have h7 := hGen R b (dialogFlagState L false D I G false H false)
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
  rw [read.2.2.2.1] at h7
  have h9 := genericFlag2_flag L hn R1 b false D I G false H false
  have hclr : ((((G ^^ (b && pointFinite R1)) ^^ D) ^^ I) ^^ H) = false := by
    rw [hR1fin]
    have hG' := hGv
    simp only [Bool.false_xor] at hG'
    rw [← hG']
    generalize (b && pointFinite R) = A
    generalize D = d at *
    generalize I = i at *
    generalize H = h at *
    cases A <;> cases d <;> cases i <;> cases h <;> rfl
  rw [hclr] at h9
  have h10a := zeroFlag_flagG L hn R1 b false D I false false H false
  rw [hR1O, Bool.false_xor] at h10a
  have readO := dialogFlagState_read L hn false D I O false H false
  have h8 := corners2_boundary L hw hn R C hC b (dialogFlagState L false D I O false H false)
    readO.2.2.2.1 readO.2.1 readO.2.2.1 readO.2.2.2.2.2.1
  have hf := dialogFlags_output b R C
  have heout : ((b && exceptionBit C) && pointEqual S (-C))=H := by
    rw [hE]
    simpa [H,S,dialogExceptionEnabled,equal_simpG] using hf.2.2.2
  have h10 := pairFlag_outputG L hw hn S C (exceptionBit C) b false D I O false H false
  rw [heout,Bool.xor_self] at h10
  simp only [equal_simpG] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := gatedFlag_D L hw hn S (C+C) (decide (cy≠-cy)) b false D I false false false false
  have hdo : ((b && decide (cy≠-cy)) && pointEqual S (C+C))=D := by
    change (K && pointEqual S (C+C)) = D
    rw [hK]; simpa only [equal_simpG] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have hzero : decide (S=0) = !pointFinite S := by
    rw [← equal_simpG]
    exact pointEqual_zero S
  have h12 := chainErase_equalI L hn S b false false (dialogInversePoint b R C)
    false false false false (by rw [← hf.2.2.1, hzero])
  have h := ((((((((h3.seq h5).seq h6).seq h7).seq h9).seq h10a).seq h8).seq h10).seq h11).seq h12
  simpa only [finiteProgramFG,List.append_assoc,dialogFlagState_zero] using h

end SpecFG

end ECDSAAdd.Entrant
