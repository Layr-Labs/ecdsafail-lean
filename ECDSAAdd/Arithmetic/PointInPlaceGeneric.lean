import ECDSAAdd.Arithmetic.PointInPlaceClearSlope

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 普通分支为真时的原地公式；例外斜率条件由曲线点数学引理提供。 -/
theorem pointInPlaceGeneric_true (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy k : Fp) (hX : X≠cx)
    (hk : cx-genericX X Y cx cy=0 → genericSlope X Y cx cy=k) :
    Triple (PointInPlaceValues L X Y 0 true false false) (pointInPlaceGeneric L cx cy k)
      (PointInPlaceValues L (genericX X Y cx cy) (genericY X Y cx cy) 0 true false false) := by
  let a := genericSlope X Y cx cy
  let d := cx-genericX X Y cx cy
  have hv := generic_inplace_values X Y cx cy hX
  have h1 := pointStep_addX L hw hn X Y 0 true false false (-cx)
  have h2 := pointStep_addY L hw hn (X-cx) Y 0 true false false (-cy)
  simp only [if_true,← sub_eq_add_neg] at h1 h2
  have h3 := pointStep_divideAdd L hw hn (X-cx) (Y-cy) 0 true false false
    (fun _ => sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a := by rfl
  simp only [if_true,zero_add,ha] at h3
  have h4 := (pointStep_product L hw hn (X-cx) (Y-cy) a true false false).2
  rw [show (Y-cy)-a*(X-cx)=0 from hv.1] at h4
  have h5 := pointStep_square L hw hn (X-cx) 0 a true false false
  have h6 := pointStep_addX L hw hn ((X-cx)-a*a) 0 a true false false (3*cx)
  simp only [if_true] at h6
  rw [show (X-cx)-a*a+3*cx=d from hv.2.1] at h6
  have h7 := (pointStep_product L hw hn d 0 a true false false).1
  simp only [zero_add] at h7
  have h8 := pointInPlaceClearSlope_spec L hw hn d (a*d) a k true (fun _ => rfl)
    (fun _ hd => hk hd) (by simp)
  have h9 := pointStep_negate L hw hn d (a*d) 0 true false false
  simp only [if_true] at h9
  have h10 := pointStep_addX L hw hn (-d) (a*d) 0 true false false cx
  simp only [if_true] at h10
  rw [show -d+cx=genericX X Y cx cy by dsimp [d]; ring] at h10
  have h11 := pointStep_addY L hw hn (genericX X Y cx cy) (a*d) 0 true false false (-cy)
  simp only [if_true,← sub_eq_add_neg] at h11
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at h11
  have h := (((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11
  simpa only [pointInPlaceGeneric,List.append_assoc] using h

/-- 未选中的分支斜率始终为零，仍执行同一固定门列并恢复全部工作区。 -/
theorem pointInPlaceGeneric_false (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y cx cy k : Fp) :
    Triple (PointInPlaceValues L X Y 0 false false false) (pointInPlaceGeneric L cx cy k)
      (PointInPlaceValues L X Y 0 false false false) := by
  have h1 := pointStep_addX L hw hn X Y 0 false false false (-cx)
  have h2 := pointStep_addY L hw hn X Y 0 false false false (-cy)
  have h3 := pointStep_divideAdd L hw hn X Y 0 false false false (by simp)
  have h4 := (pointStep_product L hw hn X Y 0 false false false).2
  have h5 := pointStep_square L hw hn X Y 0 false false false
  have h6 := pointStep_addX L hw hn X Y 0 false false false (3*cx)
  have h7 := (pointStep_product L hw hn X Y 0 false false false).1
  have h8 := pointInPlaceClearSlope_spec L hw hn X Y 0 k false (by simp) (by simp) (by simp)
  have h9 := pointStep_negate L hw hn X Y 0 false false false
  have h10 := pointStep_addX L hw hn X Y 0 false false false cx
  have h11 := pointStep_addY L hw hn X Y 0 false false false (-cy)
  simp only [Bool.false_eq_true,if_false,add_zero,zero_mul,sub_zero] at h1 h2 h3 h4 h5 h6 h7 h9 h10 h11
  have h := (((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11
  simpa only [pointInPlaceGeneric,List.append_assoc] using h

end ECDSAAdd.Arithmetic
