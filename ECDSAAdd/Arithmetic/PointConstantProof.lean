import ECDSAAdd.Arithmetic.PointEffect

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem pointFinite_effect (c : Wire) (r : PointReg) (F : Bool)
    (hn : (PointAddLayout.pointWires r).Nodup) (s : State) (m : List Bool) :
    PointEffect r (s.basis c && F) 0 0 s
      (run (maskedConstant c [r.finite] F.toNat) m s) := by
  have hh : run (maskedConstant c [r.finite] F.toNat) m s=
      ⟨s.phase,writeBit s.basis r.finite (s.basis r.finite ^^ (s.basis c && F))⟩ := by
    cases F <;> simp [maskedConstant,run,writeBit]
  rw [hh]
  apply PointEffect.of_finite r hn
  · rfl
  · intro w hw; simp [writeBit,hw]
  · simp [writeBit]

theorem maskedPointConstant_correct (c : Wire) (r : PointReg) (C : Point)
    (hn : (PointAddLayout.pointWires r).Nodup) (hc : c∉PointAddLayout.pointWires r)
    (hx : r.x.length=256) (hy : r.y.length=256) (s : State) (m : List Bool) :
    PointEffect r (s.basis c && pointFinite C)
      (if s.basis c then pointX C else 0) (if s.basis c then pointY C else 0) s
      (run (maskedPointConstant c r C) m s) := by
  have nr := List.nodup_append'.mp (List.nodup_cons.mp hn).2
  have hcx : c∉r.x := fun hw => hc (by simp [PointAddLayout.pointWires,hw])
  have hcy : c∉r.y := fun hw => hc (by simp [PointAddLayout.pointWires,hw])
  have bx : pointX C<2^r.x.length := by
    rw [hx]; exact lt_trans (point_coordinates_lt C).1 (by norm_num [p])
  have by' : pointY C<2^r.y.length := by
    rw [hy]; exact lt_trans (point_coordinates_lt C).2 (by norm_num [p])
  let u := run (maskedConstant c [r.finite] (pointFinite C).toNat) m s
  have e0 := pointFinite_effect c r (pointFinite C) hn s m
  have uc : u.basis c=s.basis c := e0.outside c hc
  obtain ⟨px,ex,vx⟩ := maskedConstant_correct c r.x (pointX C) nr.1 hcx bx u m
  have e1 := PointEffect.of_x r hn _ u _ px ex vx
  let v := run (maskedConstant c r.x (pointX C)) m u
  have vc : v.basis c=s.basis c := (e1.outside c hc).trans uc
  obtain ⟨py,ey,vy⟩ := maskedConstant_correct c r.y (pointY C) nr.2.1 hcy by' v m
  have e2 := PointEffect.of_y r hn _ v _ py ey vy
  have he := e0.trans (e1.trans e2)
  rw [maskedPointConstant,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(maskedConstant_counts _ _ _).2,Nat.zero_add,List.drop_zero]
  simpa only [u,v,uc,vc,Bool.xor_false,Nat.zero_xor,Nat.xor_zero] using he

end ECDSAAdd.Arithmetic
