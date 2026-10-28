import ECDSAAdd.Baselines.SlotCompressed
import ECDSAAdd.Baselines.SlotStreamedSquare
import ECDSAAdd.Baselines.SlotRecovery
import ECDSAAdd.Baselines.ValueWalkSlots

namespace ECDSAAdd.Baselines
open Arithmetic Challenge Secp256k1 MappedCompressed

theorem skywalkSquare_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    gateSlots (CompressedPointSquare.computableProgram L) ≤ 5000000 := by
  simpa only [CompressedPointSquare.computableProgram,rename_gateSlots,pointMeasuredSquareCandidate]
    using measuredProgram_gateSlots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) L.core.generic

theorem skywalkGeneric_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths)
    (cx cy : Fp) : gateSlots (pointCompressedDialogGeneric L cx cy) ≤ 46300000 := by
  have a := recoveryConstant_gateSlots_le L hw L.point.x hw.inputX (-cx)
  have b := recoveryConstant_gateSlots_le L hw L.point.y hw.inputY (-cy)
  have c := recoveryConstant_gateSlots_le L hw L.point.x hw.inputX (3*cx)
  have d := pointCompressedArithmetic_gateSlots_le L false
  have e := pointCompressedArithmetic_gateSlots_le L true
  have f := skywalkSquare_gateSlots_le L hw
  have g := recoveryStage_gateSlots_le L hw cx cy
  simp only [pointCompressedDialogGeneric,gateSlots_append]; omega

theorem skywalkFinite_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths)
    (C : Point) (cx cy : Fp) : gateSlots (pointCompressedDialogFinite L C cx cy) ≤ 47000000 := by
  have hg := skywalkGeneric_gateSlots_le L hw cx cy
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have hpl : (PointAddLayout.pointWires L.point).length = 513 := by
    simp [PointAddLayout.pointWires, hx, hy]
  have hzl : L.dialogPointZero.length = 513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp only [List.length_take,L.dialogPool_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have hz c t k : gateSlots (equalConstant c t L.dialogPointZero k) ≤ 4618 := by
    have h := equalConstant_gateSlots_le c t L.dialogPointZero k
    rw [hzl] at h; exact h
  have hm c P : gateSlots (maskedPointConstant c L.point P) ≤ 513 := by
    have h := maskedPoint_gateSlots_le c L.point P
    rw [hx,hy] at h; exact h
  have he : gateSlots (pointInPlaceDoubleEnable L cy) ≤ 1 := by
    unfold pointInPlaceDoubleEnable; split <;> simp [gateSlots_cons, instructionSlots]
  have hh : gateSlots (pointDialogExceptionEnable L C) ≤ 1 := by
    unfold pointDialogExceptionEnable; split <;> simp [gateSlots_cons, instructionSlots]
  have hf : gateSlots (pointDialogGenericFlag L) = 5 := rfl
  have z1 := hz L.control L.infinitySelect (pointCode 0)
  have z2 := hz L.core.double L.doubleSelect (pointCode C)
  have z3 := hz L.control L.genericSelect (pointCode (-C))
  have z4 := hz L.core.equalX L.core.equalNegY (pointCode (dialogExceptionPoint C))
  have z5 := hz L.control L.infinitySelect (pointCode C)
  have z6 := hz L.core.double L.doubleSelect (pointCode (C+C))
  have z7 := hz L.control L.genericSelect (pointCode 0)
  have z8 := hz L.core.equalX L.core.equalNegY (pointCode (-C))
  have m1 := hm L.infinitySelect C
  have m2 := hm L.doubleSelect C
  have m3 := hm L.doubleSelect (C+C)
  have m4 := hm L.genericSelect (-C)
  have m5 := hm L.core.equalNegY (dialogExceptionPoint C)
  have m6 := hm L.core.equalNegY (-C)
  simp only [pointCompressedDialogFinite, pointDialogCorners, pointInPlaceCorners, gateSlots_append, hf]
  omega

theorem normalizedSkywalk_gateSlots_le (C : Point) :
    gateSlots (normalizedSkywalk C) ≤ 47000000 := by
  rw [normalizedSkywalk, normalize_gateSlots]
  cases C with
  | zero => simp [skywalk, Submissions.Skywalk.program, controlledPointAdd]
  | some hp => exact skywalkFinite_gateSlots_le layout layout_widths _ _ _

end ECDSAAdd.Baselines
