import ECDSAAdd.Arithmetic.PointDialogProgram
import ECDSAAdd.Arithmetic.PointOutputResources
import ECDSAAdd.Arithmetic.SquareSubResources
import ECDSAAdd.Arithmetic.OffsetBorrowedControlledPort

namespace ECDSAAdd.Arithmetic
open Secp256k1 ControlledPointLayout

/-- 常数掩码只含CX；每段成本完全来自同一模加核。 -/
theorem pointDialogConstantAdd_counts (L : ControlledPointLayout) (hw : L.Widths)
    (_hnd : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
    toffoliCount (pointDialogConstantAdd L r k)=1023 ∧
    measurementCount (pointDialogConstantAdd L r k)=1023 := by
  exact pointRecoveryConstantAdd_counts L hw r hr k

/-- Direct exact negation with shared zero/carry workspace; retained as a public utility. -/
theorem pointDialogNegate_counts (L : ControlledPointLayout) (hw : L.Widths) (_hnd : L.wires.Nodup) :
    toffoliCount (pointDialogNegate L)=1022 ∧ measurementCount (pointDialogNegate L)=1022 :=
  pointRecoveryNegate_counts L hw


theorem pointDialogSquare_counts (L : ControlledPointLayout) (hw : L.Widths) (_hn : L.wires.Nodup) :
    toffoliCount (pointDialogSquare L)=99902 ∧
      measurementCount (pointDialogSquare L)=99382 :=
  pointMeasuredSquareCandidate_counts L hw

theorem pointDialogGeneric_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) :
    toffoliCount (pointDialogGeneric L cx cy)=2216223 ∧
    measurementCount (pointDialogGeneric L cx cy)=1558291 := by
  have ha k := pointDialogConstantAdd_counts L hw hn L.point.x (Or.inl rfl) k
  have hb k := pointDialogConstantAdd_counts L hw hn L.point.y (Or.inr rfl) k
  have hd := pointOffsetBorrowedArithmetic_counts L hw hn
  have hs := pointDialogSquare_counts L hw hn
  have recovery := pointRecoveryStage_counts L hw cx cy
  simp only [pointDialogGeneric,toffoliCount_append,measurementCount_append,
    (ha _).1,(ha _).2,(hb _).1,(hb _).2,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,
    hs.1,hs.2,recovery.1,recovery.2]
  norm_num

theorem pointDialogFinite_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    toffoliCount (pointDialogFinite L C cx cy)=2220327 ∧
    measurementCount (pointDialogFinite L C cx cy)=1562395 := by
  have hg := pointDialogGeneric_counts L hw hn cx cy
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
  simp only [pointDialogFinite,pointDialogCorners,pointInPlaceCorners,toffoliCount_append,
    measurementCount_append,hg.1,hg.2,(hz _ _ _).1,(hz _ _ _).2,hzl,
    (maskedPointConstant_counts _ _ _).1,(maskedPointConstant_counts _ _ _).2,he.1,he.2,hh.1,hh.2]
  norm_num [pointDialogGenericFlag,pointInPlaceGenericFlag,toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic
