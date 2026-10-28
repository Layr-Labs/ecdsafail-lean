import ECDSAAdd.Arithmetic.ModHalf
import ECDSAAdd.Arithmetic.ModDouble
import ECDSAAdd.Arithmetic.Shift

namespace ECDSAAdd.Arithmetic

/-- 活动位控制奇偶、旋转与比较；false 分支仍执行清零算术。 -/
def controlledHalf (c : Wire) (U : ModUnaryLayout) (p : Nat) : Program :=
  [.CCX c U.bit U.flag] ++ maskedAddConst U.flag U.constant U.z U.carry U.cin p ++
  shiftRight c U.z ++
  compareLtConst (some c) U.low (U.constant.take U.low.length) U.carry U.cin U.flag ((p+1)/2) ++
  [.CX c U.flag]

/-- 独立前向加倍门列，不倒放减半的测量。 -/
def controlledDouble (c : Wire) (U : ModUnaryLayout) (p : Nat) : Program :=
  shiftLeft c U.z ++ maskedSubConst c U.constant U.z U.carry U.cin p ++
  maskedAddConst U.high (U.constant.take U.low.length) U.low
    (U.carry.take (U.low.length-1)) U.cin p ++ [.CX c U.high,.CCX c U.bit U.high]

theorem controlledUnary_counts (c : Wire) (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) (hn : 0<n) :
    toffoliCount (controlledHalf c U p)=3*n+2 ∧
    measurementCount (controlledHalf c U p)=2*n ∧
    toffoliCount (controlledDouble c U p)=3*n ∧
    measurementCount (controlledDouble c U p)=2*n-1 := by
  have hz : U.z.length=n+1 := by simp [ModUnaryLayout.z,hw.low]
  have ht : (U.constant.take U.low.length).length=n := by simp [hw.constant,hw.low]
  have hc : (U.carry.take (U.low.length-1)).length=n-1 := by simp [hw.carry,hw.low]
  have ha := addInPlace_counts U.constant U.z U.carry U.cin (hw.constant.trans hz.symm)
    (by rw [hw.carry,hz])
  have hs := subInPlace_counts U.constant U.z U.carry U.cin (hw.constant.trans hz.symm)
    (by rw [hw.carry,hz])
  have hl := addInPlace_counts (U.constant.take U.low.length) U.low
    (U.carry.take (U.low.length-1)) U.cin (ht.trans hw.low.symm)
    (by rw [hc,hw.low]; omega)
  have hm := compareLt_counts (some c) U.low (U.constant.take U.low.length) U.carry U.cin U.flag
    (hw.low.trans ht.symm) (hw.carry.trans ht.symm)
  simp only [hw.low] at hl hm
  simp only [controlledHalf,controlledDouble,maskedAddConst,maskedSubConst,
    toffoliCount_append,measurementCount_append,(shift_counts c U.z).1,
    (shift_counts c U.z).2.1,(shift_counts c U.z).2.2.1,(shift_counts c U.z).2.2.2,
    (maskedConstant_counts _ _ _).1,(maskedConstant_counts _ _ _).2,
    ha.1,ha.2,hs.1,hs.2,hl.1,hl.2,hm.1,hm.2.1,
    compareLtConst,(xorConstant_counts _ _).1,(xorConstant_counts _ _).2,toffoliCount,measurementCount,
    hz,hw.low,Option.isSome_some,if_true]
  simp only [List.length_take,hw.constant,Nat.min_eq_left (by omega : n≤n+1)]
  omega

end ECDSAAdd.Arithmetic
