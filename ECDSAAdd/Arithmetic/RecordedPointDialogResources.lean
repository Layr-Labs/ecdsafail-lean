import ECDSAAdd.Arithmetic.RecordedPointDialogSpec
import ECDSAAdd.Arithmetic.ParametricPointDialogProgram
import ECDSAAdd.Arithmetic.CompressedPointDialogResources
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedPointDialog
open ControlledPointLayout Secp256k1
theorem generic_counts (backend : RecordedPointArithmeticBackend) (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    recordedToffoliCount (generic backend L cx cy)=recordedToffoliCount (backend.program L false) + recordedToffoliCount (backend.program L true) + 105272 ∧
    recordedMeasurementCount (generic backend L cx cy)=recordedMeasurementCount (backend.program L false) + recordedMeasurementCount (backend.program L true) + 104752 := by
  have a k := pointDialogConstantAdd_counts L hw hn L.point.x (Or.inl rfl) k
  have b k := pointDialogConstantAdd_counts L hw hn L.point.y (Or.inr rfl) k
  have square := CompressedPointSquare.counts L hw
  have recovery := pointRecoveryStage_counts L hw cx cy
  simp only [generic,(recordedThen_counts _ _).1,(recordedThen_counts _ _).2,(embedRecorded_counts _).1,(embedRecorded_counts _).2,toffoliCount_append,measurementCount_append,
    (a _).1,(a _).2,(b _).1,(b _).2,
    square.1,square.2,recovery.1,recovery.2]
  omega

theorem finite_counts (backend : RecordedPointArithmeticBackend) (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    recordedToffoliCount (finite backend L C cx cy)=recordedToffoliCount (backend.program L false) + recordedToffoliCount (backend.program L true) + 109376 ∧
    recordedMeasurementCount (finite backend L C cx cy)=recordedMeasurementCount (backend.program L false) + recordedMeasurementCount (backend.program L true) + 108856 := by
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
  simp only [finite,(recordedThen_counts _ _).1,(recordedThen_counts _ _).2,(embedRecorded_counts _).1,(embedRecorded_counts _).2,pointDialogCorners,pointInPlaceCorners,toffoliCount_append,
    measurementCount_append,hg.1,hg.2,(hz _ _ _).1,(hz _ _ _).2,hzl,
    (maskedPointConstant_counts _ _ _).1,(maskedPointConstant_counts _ _ _).2,he.1,he.2,hh.1,hh.2,hf.1,hf.2]
  omega

/-- Static support bound, not a peak-live or improved-qubit claim. -/
theorem qubits_le (backend : RecordedPointArithmeticBackend) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) :
    (recordedWires (program backend L C)).card ≤ L.dialogUsedWires.toFinset.card :=
  Finset.card_le_card (program_wires backend L hw hn C)

@[simp] theorem zero_program (backend : RecordedPointArithmeticBackend) (L : ControlledPointLayout) :
    program backend L 0=[] := rfl

/-- An ordinary provider emits exactly the embedded ordinary point program. -/
theorem program_embed (backend : PointArithmeticBackend) (L : ControlledPointLayout)
    (C : Point) :
    program (RecordedPointArithmeticBackend.embed backend) L C=
      embedRecorded (ParametricPointDialog.program backend L C) := by
  cases C with
  | zero => rfl
  | some hc =>
    simp only [program,finite,generic,RecordedPointArithmeticBackend.embed,
    ParametricPointDialog.program,ParametricPointDialog.finite,ParametricPointDialog.generic,
    recordedThen_embed,List.append_assoc]

end ECDSAAdd.Arithmetic.RecordedPointDialog
