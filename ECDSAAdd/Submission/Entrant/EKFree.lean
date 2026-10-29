import ECDSAAdd.Submission.Entrant.Program
import ECDSAAdd.Submission.Entrant.QSupport

/-! Classification without the two enable flag wires.

The exception enable `E` and the doubling enable `K` are the control bit
masked by classical facts about `C`.  Instead of materialising them on the
`equalX` and `double` wires, the two comparisons they gated are driven by the
control wire and emitted only when the classical fact holds (the paired
comparisons already take these facts as classical bits).  The two wires then
stay idle, and with the arithmetic avoidance proof (`ArithAvoid.lean`) no block
touches them. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

/-- `t ^= b ∧ (point = P)`, emitted only when the classical enable holds. -/
def gatedShort (L : ControlledPointLayout) (en : Bool) (t : Wire) (P : Point) : Program :=
  if en then shortEqual L L.control t P else []

/-- The finite-addend program around an arbitrary generic-branch block `Gen`. -/
def finiteProgramEG (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  zeroFlag L.point.finite L.control L.infinitySelect ++
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  gatedShort L (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C) ++
  pointDialogGenericFlag L ++ Gen ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  pairEqual L L.infinitySelect L.core.equalNegY true (exceptionBit C) C (-C) ++
  gatedShort L (decide (cy≠-cy)) L.doubleSelect (C+C) ++
  zeroFlag L.point.finite L.control L.genericSelect

/-- Contract of a generic-branch block, as proved for the Skywalk block by
`CompressedPointDialog.boundary_generic`. -/
def GenericOK (L : ControlledPointLayout) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (Gen : Program) : Prop :=
  ∀ (R : Point) (b : Bool) (f : BasisState),
    (f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) →
    Triple (PointDialogBoundary L R b f) Gen
      (PointDialogBoundary L (if f L.core.generic then R+.some hc else R) b f)

section Flags
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem gatedShort_flag (R P : Point) (en : Bool) (t : Wire) (ht : t ∈ L.inPlaceFlags)
    (b : Bool) (f : BasisState) :
    Triple (PointDialogBoundary L R b f) (gatedShort L en t P)
      (PointDialogBoundary L R b (writeBit f t (f t ^^ ((b && en) && pointEqual R P)))) := by
  have sep := dialogFlag_separation L hn
  have hct : L.control ≠ t := fun h => (List.nodup_cons.mp sep).1 (h ▸ ht)
  cases en
  · intro s m v
    have hw' : writeBit f t (f t ^^ ((b && false) && pointEqual R P)) = f := by
      funext q; by_cases h : q = t
      · subst q; simp [writeBit]
      · simp [writeBit, h]
    rw [hw']
    exact ⟨rfl, v⟩
  · have hh := shortBoundary_equal L hw hn R P b f L.control t (Or.inl rfl) ht hct b (by simp)
    simpa only [gatedShort, if_true, Bool.and_true] using hh

theorem pairFlag_inputE (R C : Point) (cy : Fp) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (pairEqual L L.doubleSelect L.genericSelect (decide (cy ≠ -cy)) true C (-C))
      (PointDialogBoundary L R b
        (dialogFlagState L O (D ^^ ((b && decide (cy ≠ -cy)) && pointEqual R C))
          (I ^^ (b && pointEqual R (-C))) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn R C b (dialogFlagState L O D I G E H K) L.doubleSelect L.genericSelect
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    (decide (cy ≠ -cy)) true (b && decide (cy ≠ -cy)) b rfl (by simp)
  simp only [hr.2.1, hr.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K
    (D ^^ ((b && decide (cy ≠ -cy)) && pointEqual R C))).2.1
  have u2 := (dialogFlagState_update L hn O (D ^^ ((b && decide (cy ≠ -cy)) && pointEqual R C)) I G E H K
    (I ^^ (b && pointEqual R (-C)))).2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

theorem pairFlag_outputE (S C : Point) (en : Bool) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L S b (dialogFlagState L O D I G E H K))
      (pairEqual L L.infinitySelect L.core.equalNegY true en C (-C))
      (PointDialogBoundary L S b
        (dialogFlagState L (O ^^ (b && pointEqual S C)) D I G E (H ^^ ((b && en) && pointEqual S (-C))) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn S C b (dialogFlagState L O D I G E H K) L.infinitySelect L.core.equalNegY
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    true en b (b && en) (by simp) rfl
  simp only [hr.1, hr.2.2.2.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (O ^^ (b && pointEqual S C))).1
  have u2 := (dialogFlagState_update L hn (O ^^ (b && pointEqual S C)) D I G E H K
    (H ^^ ((b && en) && pointEqual S (-C)))).2.2.2.2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

theorem gatedFlag_H (R P : Point) (en : Bool) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (gatedShort L en L.core.equalNegY P)
      (PointDialogBoundary L R b (dialogFlagState L O D I G E (H ^^ ((b && en) && pointEqual R P)) K)) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := gatedShort_flag L hw hn R P en L.core.equalNegY (by simp [inPlaceFlags]) b
    (dialogFlagState L O D I G E H K)
  simp only [hr.2.2.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.2.1)

theorem gatedFlag_D (R P : Point) (en : Bool) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (gatedShort L en L.doubleSelect P)
      (PointDialogBoundary L R b (dialogFlagState L O (D ^^ ((b && en) && pointEqual R P)) I G E H K)) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := gatedShort_flag L hw hn R P en L.doubleSelect (by simp [inPlaceFlags]) b
    (dialogFlagState L O D I G E H K)
  simp only [hr.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.1)

end Flags

section Spec
attribute [local irreducible] run wires shortEqual pairEqual gatedShort pointCompressedDialogGeneric
  pointDialogGeneric MappedCompressed.pointCompressedArithmetic CompressedPointSquare.computableProgram

private theorem equal_simpE [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finiteProgramEG_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteProgramEG L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let E := b && decide (dialogExceptionEnabled C)
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : exceptionBit C = decide (dialogExceptionEnabled C) := by
    simp [exceptionBit,equal_simpE,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simpE]
  have hD : ((b && decide (cy≠-cy)) && pointEqual R C)=D := by
    change (K && pointEqual R C) = D
    rw [hK]; simp only [D,dialogDouble,equal_simpE]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simpE]
  have hH : ((b && exceptionBit C) && pointEqual R (dialogExceptionPoint C))=H := by
    rw [hE]; simp [H,dialogException,dialogExceptionEnabled,equal_simpE]
  have h2 := zeroFlag_equalO L hn R b false false false false false false false
  rw [hO,Bool.false_xor] at h2
  have h3 := pairFlag_inputE L hw hn R C cy b O false false false false false false
  rw [hD,hI,Bool.false_xor,Bool.false_xor] at h3
  have h5 := gatedFlag_H L hw hn R (dialogExceptionPoint C) (exceptionBit C) b O D I false false false false
  rw [hH,Bool.false_xor] at h5
  have h6 := dialogFlag_generic L hw hn R b O D I false false H false
  simp only [Bool.false_xor] at h6
  have read := dialogFlagState_read L hn O D I G false H false
  have h7 := hGen R b (dialogFlagState L O D I G false H false)
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
  rw [read.2.2.2.1] at h7
  have h8 := dialogBoundary_corners L hw hn R C hC b (dialogFlagState L O D I G false H false)
    read.1 read.2.1 read.2.2.1 read.2.2.2.2.2.1
  have h9 := dialogFlag_generic L hw hn S b O D I G false H false
  have hgclear : (((((G ^^ b) ^^ O) ^^ D) ^^ I) ^^ H)=false := by
    dsimp only [G,dialogOrdinary,O,D,I,H]
    generalize dialogInfinity b R=o,dialogDouble b R C=d,dialogInversePoint b R C=i,
      dialogException b R C=h
    cases b <;> cases o <;> cases d <;> cases i <;> cases h <;> rfl
  rw [hgclear] at h9
  have hf := dialogFlags_output b R C
  have heout : ((b && exceptionBit C) && pointEqual S (-C))=H := by
    rw [hE]
    simpa [E,H,S,dialogExceptionEnabled,equal_simpE] using hf.2.2.2
  have h10 := pairFlag_outputE L hw hn S C (exceptionBit C) b O D I false false H false
  rw [heout,Bool.xor_self] at h10
  simp only [equal_simpE] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := gatedFlag_D L hw hn S (C+C) (decide (cy≠-cy)) b false D I false false false false
  have hdo : ((b && decide (cy≠-cy)) && pointEqual S (C+C))=D := by
    change (K && pointEqual S (C+C)) = D
    rw [hK]; simpa only [equal_simpE] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have h12 := zeroFlag_equalI L hn S b false false I false false false false
  simp only [equal_simpE] at h12
  rw [hf.2.2.1,Bool.xor_self] at h12
  have h := ((((((((h2.seq h3).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12
  simpa only [finiteProgramEG,List.append_assoc,dialogFlagState_zero] using h

/-- The Skywalk generic block satisfies the contract. -/
theorem skywalkGeneric_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (pointCompressedDialogGeneric L cx cy) :=
  fun R b f hg => boundary_generic L hw hn R b f hc hg

end Spec

end ECDSAAdd.Entrant
