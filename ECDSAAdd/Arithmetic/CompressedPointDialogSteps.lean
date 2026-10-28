import ECDSAAdd.Arithmetic.CompressedPointDialogProgram
import ECDSAAdd.Arithmetic.PointDialogGenericPoint
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Arithmetic.CompressedPointDialog
open ControlledPointLayout Secp256k1 MappedCompressed
attribute [local irreducible] run pointCompressedArithmetic CompressedPointSquare.computableProgram
  pointMeasuredSquareCandidate

theorem step_square (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (CompressedPointSquare.computableProgram L)
      (PointDialogValues L (X-(if G then Y*Y else 0)) Y G base) := by
  intro s m v
  rw [CompressedPointSquare.state_eq L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean]
  simpa only [pointDialogSquare] using dialogStep_square L hw hn X Y G base s m v

theorem step_arithmetic (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState) (multiply : Bool) (hX : G=true → X≠0) :
    Triple (PointDialogValues L X Y G base) (pointCompressedArithmetic L multiply)
      (PointDialogValues L X (if G then (if multiply then Y*X else Y/X) else Y) G base) := by
  intro s m v
  have hX0 : G=true → X.val≠0 := by
    intro hg hx
    apply hX hg
    apply ZMod.val_injective p
    simpa using hx
  obtain ⟨phase,value,rest⟩ := pointCompressedArithmetic_correct L hw hn multiply
    X.val Y.val G X.isLt hX0 Y.isLt s m v.generic v.x v.y v.clean
  refine ⟨phase,v.withY hn ?_ rest⟩
  cases G <;> cases multiply <;>
    simpa only [Bool.false_eq_true,if_false,if_true,ZMod.natCast_zmod_val] using value

theorem generic_true (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true base) (pointCompressedDialogGeneric L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := dialogStep_addX L hw hn X Y true base (-cx)
  have h2 := dialogStep_addY L hw hn (X-cx) Y true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h1 h2
  have h3 := step_arithmetic L hw hn (X-cx) (Y-cy) true base false (fun _=>sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,Bool.false_eq_true,if_false,ha] at h3
  have h4 := step_square L hw hn (X-cx) a true base
  simp only [if_true] at h4
  have h5 := dialogStep_addX L hw hn ((X-cx)-a*a) a true base (3*cx)
  simp only [if_true] at h5
  rw [show (X-cx)-a*a+3*cx=d from hv.2.1] at h5
  have h6 := step_arithmetic L hw hn d a true base true (fun _=>hd)
  simp only [if_true] at h6
  have recovery := pointRecoveryStage_correct L hw hn d (a*d) cx cy true base
  simp only [if_true] at recovery
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at recovery
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at recovery
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq recovery
  simpa only [pointCompressedDialogGeneric,List.append_assoc] using h

theorem generic_false (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (base : BasisState) :
    Triple (PointDialogValues L X Y false base) (pointCompressedDialogGeneric L cx cy)
      (PointDialogValues L X Y false base) := by
  have h1 := dialogStep_addX L hw hn X Y false base (-cx)
  have h2 := dialogStep_addY L hw hn X Y false base (-cy)
  have h3 := step_arithmetic L hw hn X Y false base false (by simp)
  have h4 := step_square L hw hn X Y false base
  have h5 := dialogStep_addX L hw hn X Y false base (3*cx)
  have h6 := step_arithmetic L hw hn X Y false base true (by simp)
  have recovery := pointRecoveryStage_correct L hw hn X Y cx cy false base
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6 recovery
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq recovery
  simpa only [pointCompressedDialogGeneric,List.append_assoc] using h


theorem boundary_generic (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (b : Bool) (f : BasisState) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (pointCompressedDialogGeneric L cx cy)
      (PointDialogBoundary L (if f L.core.generic then R+.some hc else R) b f) := by
  intro s m v
  have hp := (point_holds _ _ _).mp v.point
  have values : PointDialogValues L ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 (f L.core.generic) s.basis s.basis :=
    ⟨hp.2.1,hp.2.2,v.flags _ (by simp [inPlaceFlags]),v.clean,fun _ _=>rfl⟩
  have hfinite : L.point.finite∉L.point.x++L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have ht := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
      beq_self_eq_true,if_true] at h ht
    omega
  have outside (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) : q∉L.point.x++L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  cases hG : f L.core.generic with
  | false =>
    rw [hG] at values
    obtain ⟨phase,hv⟩ := generic_false L hw hn _ _ cx cy s.basis s m values
    refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
    simp only [Bool.false_eq_true,if_false]
    exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩
  | true =>
    have he := hg hG
    cases R with
    | zero => exact False.elim (he.1 rfl)
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      rw [hG] at values
      obtain ⟨phase,hv⟩ := generic_true L hw hn x y cx cy s.basis den.1 den.2 s m values
      refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
      simp only [if_true,←genericAdd_correct hr hc den.1,genericAdd]
      exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩

end ECDSAAdd.Arithmetic.CompressedPointDialog
#print axioms ECDSAAdd.Arithmetic.CompressedPointDialog.generic_true
#print axioms ECDSAAdd.Arithmetic.CompressedPointDialog.boundary_generic
