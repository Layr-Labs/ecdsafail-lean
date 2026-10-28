import ECDSAAdd.Arithmetic.PointDialogBoundary
import ECDSAAdd.Arithmetic.PointInPlaceCorners

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 四次常量XOR的逐字段作用，对任意输入位串成立。 -/
theorem pointDialogCorners_effect (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) (m : List Bool) :
    PointEffect L.point
      ((((((s.basis L.infinitySelect && pointFinite C) ^^ (s.basis L.doubleSelect && pointFinite C)) ^^
        (s.basis L.doubleSelect && pointFinite (C+C))) ^^ (s.basis L.genericSelect && pointFinite (-C))) ^^
        (s.basis L.core.equalNegY && pointFinite (dialogExceptionPoint C))) ^^
        (s.basis L.core.equalNegY && pointFinite (-C)))
      ((((((if s.basis L.infinitySelect then pointX C else 0) ^^^ (if s.basis L.doubleSelect then pointX C else 0)) ^^^
        (if s.basis L.doubleSelect then pointX (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointX (-C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointX (dialogExceptionPoint C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointX (-C) else 0))
      ((((((if s.basis L.infinitySelect then pointY C else 0) ^^^ (if s.basis L.doubleSelect then pointY C else 0)) ^^^
        (if s.basis L.doubleSelect then pointY (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointY (-C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointY (dialogExceptionPoint C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointY (-C) else 0))
      s (run (pointDialogCorners L C) m s) := by
  have hr : (PointAddLayout.pointWires L.point).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    simp only [dialogUsedWires,List.count_append] at h
    omega
  have away : L.core.equalNegY∉PointAddLayout.pointWires L.point := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.equalNegY
    have hp := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,inPlaceFlags,List.count_append,List.count_cons,List.count_nil,
      beq_self_eq_true,if_true] at h
    omega
  let u := run (pointInPlaceCorners L C) m s
  have e0 := pointInPlaceCorners_effect L hw hn C s m
  have uh : u.basis L.core.equalNegY=s.basis L.core.equalNegY := e0.outside _ away
  let v := run (maskedPointConstant L.core.equalNegY L.point (dialogExceptionPoint C)) m u
  have e1 := maskedPointConstant_correct _ _ (dialogExceptionPoint C) hr away hw.inputX hw.inputY u m
  have vh : v.basis L.core.equalNegY=s.basis L.core.equalNegY := (e0.trans e1).outside _ away
  have e2 := maskedPointConstant_correct _ _ (-C) hr away hw.inputX hw.inputY v m
  have he := (e0.trans e1).trans e2
  rw [pointDialogCorners,run_append,run_take,run_append,run_take]
  simp only [pointInPlaceCorners,measurementCount_append,(maskedPointConstant_counts _ _ _).2,
    Nat.add_zero,List.drop_zero]
  simpa only [uh,vh] using he

/-- 输入分类确定的四次XOR将普通分支输出或角落输入统一写为受控平移结果。 -/
theorem dialogBoundary_corners [DecidableEq Point] (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R C : Point) (hc : C≠0) (b : Bool) (f : BasisState)
    (ho : f L.infinitySelect=dialogInfinity b R)
    (hd : f L.doubleSelect=dialogDouble b R C)
    (hi : f L.genericSelect=dialogInversePoint b R C)
    (hh : f L.core.equalNegY=dialogException b R C) :
    Triple (PointDialogBoundary L (if dialogOrdinary b R C then R+C else R) b f)
      (pointDialogCorners L C) (PointDialogBoundary L (if b then R+C else R) b f) := by
  intro s m v
  have he := pointDialogCorners_effect L hw hn C s m
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

end ECDSAAdd.Arithmetic
