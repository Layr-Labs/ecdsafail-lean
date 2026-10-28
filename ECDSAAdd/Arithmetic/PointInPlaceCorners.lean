import ECDSAAdd.Arithmetic.PointInPlaceBoundarySteps

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 四次常量XOR的逐字段作用，对任意输入位串成立。 -/
theorem pointInPlaceCorners_effect (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) (m : List Bool) :
    PointEffect L.point
      ((((s.basis L.infinitySelect && pointFinite C) ^^ (s.basis L.doubleSelect && pointFinite C)) ^^
        (s.basis L.doubleSelect && pointFinite (C+C))) ^^ (s.basis L.genericSelect && pointFinite (-C)))
      ((((if s.basis L.infinitySelect then pointX C else 0) ^^^ (if s.basis L.doubleSelect then pointX C else 0)) ^^^
        (if s.basis L.doubleSelect then pointX (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointX (-C) else 0))
      ((((if s.basis L.infinitySelect then pointY C else 0) ^^^ (if s.basis L.doubleSelect then pointY C else 0)) ^^^
        (if s.basis L.doubleSelect then pointY (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointY (-C) else 0))
      s (run (pointInPlaceCorners L C) m s) := by
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
  have ho := away L.infinitySelect (by simp [inPlaceFlags])
  have hd := away L.doubleSelect (by simp [inPlaceFlags])
  have hi := away L.genericSelect (by simp [inPlaceFlags])
  let u := run (maskedPointConstant L.infinitySelect L.point C) m s
  have e0 := maskedPointConstant_correct _ _ C hr ho hw.inputX hw.inputY s m
  have ud : u.basis L.doubleSelect=s.basis L.doubleSelect := e0.outside _ hd
  let v := run (maskedPointConstant L.doubleSelect L.point C) m u
  have e1 := maskedPointConstant_correct _ _ C hr hd hw.inputX hw.inputY u m
  have vd : v.basis L.doubleSelect=s.basis L.doubleSelect := (e0.trans e1).outside _ hd
  let w := run (maskedPointConstant L.doubleSelect L.point (C+C)) m v
  have e2 := maskedPointConstant_correct _ _ (C+C) hr hd hw.inputX hw.inputY v m
  have wi : w.basis L.genericSelect=s.basis L.genericSelect := ((e0.trans e1).trans e2).outside _ hi
  have e3 := maskedPointConstant_correct _ _ (-C) hr hi hw.inputX hw.inputY w m
  have hh := ((e0.trans e1).trans e2).trans e3
  rw [pointInPlaceCorners,run_append,run_take,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(maskedPointConstant_counts _ _ _).2,Nat.zero_add,List.drop_zero]
  simpa only [ud,vd,wi] using hh

/-- 输入分类确定的四次XOR将普通分支输出或角落输入统一写为受控平移结果。 -/
theorem pointBoundary_corners (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R C : Point) (hc : C≠0) (b : Bool) (f : BasisState)
    (ho : f L.infinitySelect=inPlaceInfinity b R)
    (hd : f L.doubleSelect=inPlaceDouble b R C)
    (hi : f L.genericSelect=inPlaceInversePoint b R C) :
    Triple (PointInPlaceBoundary L (if inPlaceOrdinary b R C then R+C else R) b f)
      (pointInPlaceCorners L C) (PointInPlaceBoundary L (if b then R+C else R) b f) := by
  intro s m v
  have he := pointInPlaceCorners_effect L hw hn C s m
  have vo := (v.flags _ (by simp [inPlaceFlags])).trans ho
  have vd := (v.flags _ (by simp [inPlaceFlags])).trans hd
  have vi := (v.flags _ (by simp [inPlaceFlags])).trans hi
  have hp := (point_holds _ _ _).mp v.point
  refine ⟨he.phase,v.withPoint hw hn ((point_holds _ _ _).mpr ⟨?_,?_,?_⟩) he.outside⟩
  · rw [he.finite,hp.1,vo,vd,vi]
    have h := inPlaceCorners_bool b R C hc pointFinite (by rfl)
    have bool_if (a b : Bool) : (if a then b else false)=(a && b) := by cases a <;> rfl
    simpa only [bool_if,Bool.xor_assoc] using h
  · rw [he.x,hp.2.1,vo,vd,vi]
    simpa only [Nat.xor_assoc] using inPlaceCorners_nat b R C hc pointX (by rfl)
  · rw [he.y,hp.2.2,vo,vd,vi]
    simpa only [Nat.xor_assoc] using inPlaceCorners_nat b R C hc pointY (by rfl)

end ECDSAAdd.Arithmetic
