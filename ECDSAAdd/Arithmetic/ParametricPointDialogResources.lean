import ECDSAAdd.Arithmetic.ParametricPointDialogSpec
import ECDSAAdd.Arithmetic.CompressedPointDialogResources
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.ParametricPointDialog
open ControlledPointLayout Secp256k1
theorem generic_counts (backend : PointArithmeticBackend) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    toffoliCount (generic backend L cx cy)=toffoliCount (backend.program L false) + toffoliCount (backend.program L true) + 105272 ∧
    measurementCount (generic backend L cx cy)=measurementCount (backend.program L false) + measurementCount (backend.program L true) + 104752 := by
  have a k := pointDialogConstantAdd_counts L hw hn L.point.x (Or.inl rfl) k
  have b k := pointDialogConstantAdd_counts L hw hn L.point.y (Or.inr rfl) k
  have square := CompressedPointSquare.counts L hw
  have recovery := pointRecoveryStage_counts L hw cx cy
  simp only [generic,toffoliCount_append,measurementCount_append,
    (a _).1,(a _).2,(b _).1,(b _).2,
    square.1,square.2,recovery.1,recovery.2]
  omega

theorem finite_counts (backend : PointArithmeticBackend) (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    toffoliCount (finite backend L C cx cy)=toffoliCount (backend.program L false) + toffoliCount (backend.program L true) + 109376 ∧
    measurementCount (finite backend L C cx cy)=measurementCount (backend.program L false) + measurementCount (backend.program L true) + 108856 := by
  have hg := generic_counts backend L hw hn cx cy
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
  have hf : toffoliCount (pointDialogGenericFlag L)=0 ∧
      measurementCount (pointDialogGenericFlag L)=0 := by
    norm_num [pointDialogGenericFlag,pointInPlaceGenericFlag,toffoliCount,measurementCount]
  simp only [finite,pointDialogCorners,pointInPlaceCorners,toffoliCount_append,
    measurementCount_append,hg.1,hg.2,(hz _ _ _).1,(hz _ _ _).2,hzl,
    (maskedPointConstant_counts _ _ _).1,(maskedPointConstant_counts _ _ _).2,he.1,he.2,hh.1,hh.2,hf.1,hf.2]
  omega

/-- Static support bound, not a peak-live or improved-qubit claim. -/
theorem qubits_le (backend : PointArithmeticBackend) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) :
    qubitCount (program backend L C) ≤ L.dialogUsedWires.toFinset.card :=
  Finset.card_le_card (program_wires backend L hw hn C)

@[simp] theorem zero_program (backend : PointArithmeticBackend) (L : ControlledPointLayout) :
    program backend L 0=[] := rfl

end ECDSAAdd.Arithmetic.ParametricPointDialog
