import ECDSAAdd.Arithmetic.PointInPlaceLayoutProof
import ECDSAAdd.Arithmetic.PointInPlaceProgram
import ECDSAAdd.Arithmetic.PointOutputResources
import ECDSAAdd.Arithmetic.SquareSubResources

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout

/-- 常数掩码只含CX；每段成本完全来自同一模加核。 -/
theorem pointInPlaceConstantAdd_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
    toffoliCount (pointInPlaceConstantAdd L r k)=1023 ∧
    measurementCount (pointInPlaceConstantAdd L r k)=1023 := by
  have hn : (L.inPlaceConstant r).wires.Nodup := by
    rcases hr with rfl | rfl
    · exact (L.inPlaceConstant_nodup hw hnd).1
    · exact (L.inPlaceConstant_nodup hw hnd).2
  have hl : r.length=256 := by
    rcases hr with rfl | rfl
    · exact hw.inputX
    · exact hw.inputY
  have ha := modAddInPlace_resources (L.inPlaceConstant r) 256 p (L.inPlaceConstant_widths hw r hl) hn (by omega)
  simp only [pointInPlaceConstantAdd,toffoliCount_append,measurementCount_append,
    (maskedConstant_counts _ _ _).1,(maskedConstant_counts _ _ _).2,ha.1,ha.2.1]
  norm_num

/-- T←−x、受控交换、T+=x的同门列计数。 -/
theorem pointInPlaceNegate_counts (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    toffoliCount (pointInPlaceNegate L)=3838 ∧ measurementCount (pointInPlaceNegate L)=2558 := by
  have hn := L.inPlaceNegate_nodup hw hnd
  have hl := L.inPlaceNegate_widths hw
  have ha := controlledModAdd_resources L.core.generic L.inPlaceNegate 256 p hl hn (by omega)
  have hs := controlledModSub_resources L.core.generic L.inPlaceNegate 256 p hl hn (by omega)
  have hswap : (L.core.generic::L.point.x++L.inPlaceNegate.low).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [inPlaceNegate, ModInPlaceLayout.wires,ModInPlaceLayout.z,ModUnaryLayout.core,
      ModAddCoreLayout.z,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have he := swapRegisters_resources L.core.generic L.point.x L.inPlaceNegate.low
    (hw.inputX.trans hl.core.low.symm) hswap
  simp only [pointInPlaceNegate,toffoliCount_append,measurementCount_append,ha.1,ha.2.1,hs.1,hs.2.1,he.1,he.2]
  rw [show L.point.x.length=256 from hw.inputX]
  norm_num

/-- 与§16逐门预算对应的普通分支精确门数；尚不替代其功能规格。 -/
theorem pointInPlaceGeneric_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (cx cy lambdaStar : Fp) :
    toffoliCount (pointInPlaceGeneric L cx cy lambdaStar)=8810556 ∧
    measurementCount (pointInPlaceGeneric L cx cy lambdaStar)=5643068 := by
  have ha k := pointInPlaceConstantAdd_counts L hw hnd L.point.x (Or.inl rfl) k
  have hb k := pointInPlaceConstantAdd_counts L hw hnd L.point.y (Or.inr rfl) k
  have hd c (hc : c∈L.inPlaceFlags) := divide_counts (L.inPlaceDivide c L.point.x L.point.y)
    (L.inPlaceDivide_widths hw c _ _ hw.inputX hw.inputY) (L.inPlaceDivide_nodup hw hnd c hc)
  have hdg := hd L.core.generic (by simp [inPlaceFlags])
  have hdq := hd L.core.equalNegY (by simp [inPlaceFlags])
  have hm := montAdapter_counts L.inPlaceMultiply p (L.inPlaceMultiply_widths hw)
    (L.inPlaceMultiply_nodup hw hnd)
  have hs := squareSub_counts L.inPlaceKaratsuba (L.inPlaceKaratsuba_widths hw)
    (L.inPlaceKaratsuba_nodup hw hnd)
  have hz := equalConstant_counts L.core.generic L.core.equalX L.inPlaceXZero 0
  have hzl : L.inPlaceXZero.length=256 := by
    have he := (zeroPorts_maps L.point.x (L.inPlaceBorrow.take 256)
      (by simp only [List.length_take,L.inPlaceBorrow_length hw]; exact hw.inputX)).1
    have hh := congrArg List.length he
    simpa only [List.length_map,show L.point.x.length=256 from hw.inputX] using hh
  rw [hzl] at hz
  have hn := pointInPlaceNegate_counts L hw hnd
  simp only [pointInPlaceGeneric,pointInPlaceClearSlope,toffoliCount_append,measurementCount_append,
    (ha _).1,(ha _).2,(hb _).1,(hb _).2,hdg.1,hdg.2.1,hdq.2.2.1,hdq.2.2.2,
    hm.2.1.1,hm.2.1.2,hm.2.2.1,hm.2.2.2,hs.1,hs.2,hz.1,hz.2,hn.1,hn.2,(maskedConstant_counts _ _ _).1,(maskedConstant_counts _ _ _).2]
  norm_num [toffoliCount,measurementCount]

/-- 分类与输出清标志各做三次完整点检测；常量写回不含Toffoli。 -/
theorem pointInPlaceFinite_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    toffoliCount (pointInPlaceFinite L C cx cy)=8813634 ∧
    measurementCount (pointInPlaceFinite L C cx cy)=5646146 := by
  have hg := pointInPlaceGeneric_counts L hw hnd cx cy (exceptionalSlope C)
  have hz c t k := equalConstant_counts c t L.inPlacePointZero k
  have hpl : (PointAddLayout.pointWires L.point).length=513 := by
    simp only [PointAddLayout.pointWires,List.length_cons,List.length_append,
      show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY]
  have hzl : L.inPlacePointZero.length=513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.inPlaceBorrow.take 513)
      (by simp only [List.length_take,L.inPlaceBorrow_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have he : toffoliCount (pointInPlaceDoubleEnable L cy)=0 ∧
      measurementCount (pointInPlaceDoubleEnable L cy)=0 := by
    unfold pointInPlaceDoubleEnable
    split <;> simp [toffoliCount,measurementCount]
  simp only [pointInPlaceFinite,pointInPlaceCorners,toffoliCount_append,measurementCount_append,hg.1,hg.2,
    (hz _ _ _).1,(hz _ _ _).2,hzl,(maskedPointConstant_counts _ _ _).1,
    (maskedPointConstant_counts _ _ _).2,he.1,he.2]
  norm_num [pointInPlaceGenericFlag,toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic
