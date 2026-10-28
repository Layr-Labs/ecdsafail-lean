import ECDSAAdd.Arithmetic.PointDialogProgram

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

theorem pointDialogGeneric_true (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (base : BasisState) (hX : X≠cx) (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true base) (pointDialogGeneric L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true base) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := dialogStep_addX L hw hn X Y true base (-cx)
  have h2 := dialogStep_addY L hw hn (X-cx) Y true base (-cy)
  simp only [if_true,←sub_eq_add_neg] at h1 h2
  have h3 := dialogStep_arithmetic L hw hn (X-cx) (Y-cy) true base false (fun _=>sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := rfl
  simp only [if_true,Bool.false_eq_true,if_false,ha] at h3
  have h4 := dialogStep_square L hw hn (X-cx) a true base
  simp only [if_true] at h4
  have h5 := dialogStep_addX L hw hn ((X-cx)-a*a) a true base (3*cx)
  simp only [if_true] at h5
  rw [show (X-cx)-a*a+3*cx=d from hv.2.1] at h5
  have h6 := dialogStep_arithmetic L hw hn d a true base true (fun _=>hd)
  simp only [if_true] at h6
  have recovery := pointRecoveryStage_correct L hw hn d (a*d) cx cy true base
  simp only [if_true] at recovery
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at recovery
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at recovery
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq recovery
  simpa only [pointDialogGeneric,List.append_assoc] using h

theorem pointDialogGeneric_false (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy : Fp) (base : BasisState) :
    Triple (PointDialogValues L X Y false base) (pointDialogGeneric L cx cy)
      (PointDialogValues L X Y false base) := by
  have h1 := dialogStep_addX L hw hn X Y false base (-cx)
  have h2 := dialogStep_addY L hw hn X Y false base (-cy)
  have h3 := dialogStep_arithmetic L hw hn X Y false base false (by simp)
  have h4 := dialogStep_square L hw hn X Y false base
  have h5 := dialogStep_addX L hw hn X Y false base (3*cx)
  have h6 := dialogStep_arithmetic L hw hn X Y false base true (by simp)
  have recovery := pointRecoveryStage_correct L hw hn X Y cx cy false base
  simp only [Bool.false_eq_true,if_false,if_true,add_zero,sub_zero] at h1 h2 h3 h4 h5 h6 recovery
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq recovery
  simpa only [pointDialogGeneric,List.append_assoc] using h

end ECDSAAdd.Arithmetic
