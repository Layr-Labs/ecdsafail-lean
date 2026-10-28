/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
import ECDSAAdd.Arithmetic.ValueWalkPointProgram
import ECDSAAdd.Arithmetic.PointOutputResources
import ECDSAAdd.Arithmetic.SquareSubResources

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout

/-- 常数掩码只含CX；每段成本完全来自同一模加核。 -/
theorem valueWalkPointDialogConstantAdd_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
    toffoliCount (valueWalkPointDialogConstantAdd L r k)=1023 ∧
    measurementCount (valueWalkPointDialogConstantAdd L r k)=1023 := by
  have hn := (List.nodup_cons.mp (L.dialogUnary_nodup hw hnd r hr)).2
  have hl : r.length=256 := by
    rcases hr with rfl | rfl
    · exact hw.inputX
    · exact hw.inputY
  have ha := modAddInPlace_resources (L.dialogUnary r) 256 p (L.dialogUnary_widths hw r hl) hn (by omega)
  simp only [valueWalkPointDialogConstantAdd,toffoliCount_append,measurementCount_append,
    (maskedConstant_counts _ _ _).1,(maskedConstant_counts _ _ _).2,ha.1,ha.2.1]
  norm_num

/-- T←−x、受控交换、T+=x的同门列计数。 -/
theorem valueWalkPointDialogNegate_counts (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    toffoliCount (valueWalkPointDialogNegate L)=3838 ∧ measurementCount (valueWalkPointDialogNegate L)=2558 := by
  have hn := L.dialogNegate_nodup hw hnd
  have hl := L.dialogNegate_widths hw
  have ha := controlledModAdd_resources L.core.generic L.dialogNegate 256 p hl hn (by omega)
  have hs := controlledModSub_resources L.core.generic L.dialogNegate 256 p hl hn (by omega)
  have hswap : (L.core.generic::L.point.x++L.dialogNegate.low).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [dialogNegate, ModInPlaceLayout.wires,ModInPlaceLayout.z,
      ModAddCoreLayout.z,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have he := swapRegisters_resources L.core.generic L.point.x L.dialogNegate.low
    (hw.inputX.trans hl.core.low.symm) hswap
  simp only [valueWalkPointDialogNegate,toffoliCount_append,measurementCount_append,ha.1,ha.2.1,hs.1,hs.2.1,he.1,he.2]
  rw [show L.point.x.length=256 from hw.inputX]
  norm_num


theorem valueWalkPointDialogSquare_counts (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    toffoliCount (valueWalkPointDialogSquare L)=275641 ∧ measurementCount (valueWalkPointDialogSquare L)=275129 := by
  have hc := copyRegister_counts (some L.core.generic) L.point.y (L.dialogPool.take 256)
    (by simp [show L.point.y.length=256 from hw.inputY,L.dialogPool_length hw])
  have hs := squareSub_counts L.dialogSquare (L.dialogSquare_widths hw) (L.dialogSquare_nodup hw hn)
  simp only [valueWalkPointDialogSquare,toffoliCount_append,measurementCount_append,hc.1,hc.2,hs.1,hs.2]
  rw [show L.point.y.length=256 from hw.inputY]
  norm_num

theorem valueWalkPointDialogGeneric_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) :
    toffoliCount (valueWalkPointDialogGeneric L cx cy)=6282702 ∧
    measurementCount (valueWalkPointDialogGeneric L cx cy)=3775170 := by
  have ha k := valueWalkPointDialogConstantAdd_counts L hw hn L.point.x (Or.inl rfl) k
  have hb k := valueWalkPointDialogConstantAdd_counts L hw hn L.point.y (Or.inr rfl) k
  have hd := dialog_counts L.dialogPort p (DialogLayout.fromPool_widths _ _ _ _) (L.dialogPort_nodup hw hn)
  have hs := valueWalkPointDialogSquare_counts L hw hn
  have hn' := valueWalkPointDialogNegate_counts L hw hn
  simp only [valueWalkPointDialogGeneric,toffoliCount_append,measurementCount_append,
    (ha _).1,(ha _).2,(hb _).1,(hb _).2,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,
    hs.1,hs.2,hn'.1,hn'.2]
  norm_num

theorem valueWalkPointDialogFinite_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    toffoliCount (valueWalkPointDialogFinite L C cx cy)=6286806 ∧
    measurementCount (valueWalkPointDialogFinite L C cx cy)=3779274 := by
  have hg := valueWalkPointDialogGeneric_counts L hw hn cx cy
  have hz c t k := equalConstant_counts c t L.dialogPointZero k
  have hpl : (PointAddLayout.pointWires L.point).length=513 := by
    simp only [PointAddLayout.pointWires,List.length_cons,List.length_append,
      show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY]
  have hzl : L.dialogPointZero.length=513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp only [List.length_take,L.dialogPool_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have he : toffoliCount (pointInPlaceDoubleEnable L cy)=0 ∧
      measurementCount (pointInPlaceDoubleEnable L cy)=0 := by
    unfold pointInPlaceDoubleEnable
    split <;> simp [toffoliCount,measurementCount]
  have hh : toffoliCount (pointDialogExceptionEnable L C)=0 ∧
      measurementCount (pointDialogExceptionEnable L C)=0 := by
    unfold pointDialogExceptionEnable
    split <;> simp [toffoliCount,measurementCount]
  simp only [valueWalkPointDialogFinite,pointDialogCorners,pointInPlaceCorners,toffoliCount_append,
    measurementCount_append,hg.1,hg.2,(hz _ _ _).1,(hz _ _ _).2,hzl,
    (maskedPointConstant_counts _ _ _).1,(maskedPointConstant_counts _ _ _).2,he.1,he.2,hh.1,hh.2]
  norm_num [pointDialogGenericFlag,pointInPlaceGenericFlag,toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic
