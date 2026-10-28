import ECDSAAdd.Baselines.SlotDialog
import ECDSAAdd.Baselines.SlotSquare

namespace ECDSAAdd.Baselines
open Arithmetic Challenge Secp256k1

theorem valueWalkConstant_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths)
    (r : List Wire) (hr : r.length = 256) (k : Fp) :
    gateSlots (valueWalkPointDialogConstantAdd L r k) ≤ 14500 := by
  have hl := L.dialogUnary_widths hw r hr
  have ha := modAddCore_gateSlots_le (L.dialogUnary r).toModAddCoreLayout p
  have hm := maskedConstant_gateSlots_le L.core.generic (L.dialogUnary r).a k.val
  rw [hl.core.a, hl.core.constant, hl.core.low] at ha
  rw [hl.core.a] at hm
  simp only [valueWalkPointDialogConstantAdd, modAddInPlace, gateSlots_append]; omega

theorem valueWalkNegate_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    gateSlots (valueWalkPointDialogNegate L) ≤ 38000 := by
  have hl := L.dialogNegate_widths hw
  have hm := controlledMod_gateSlots_le L.core.generic L.dialogNegate 256 p hl
  simp only [valueWalkPointDialogNegate, gateSlots_append, swapRegisters_gateSlots, hl.core.low]
  omega

theorem valueWalkSquare_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    gateSlots (valueWalkPointDialogSquare L) ≤ 6500512 := by
  have h := squareSub_gateSlots_le L.dialogSquare (L.dialogSquare_widths hw) (L.dialogSquare_nodup hw hn)
  simp only [valueWalkPointDialogSquare, gateSlots_append, copyRegister_gateSlots,
    List.length_take, L.dialogPool_length hw]
  omega

theorem valueWalkGeneric_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : gateSlots (valueWalkPointDialogGeneric L cx cy) ≤ 60700000 := by
  have hx k := valueWalkConstant_gateSlots_le L hw L.point.x hw.inputX k
  have hy k := valueWalkConstant_gateSlots_le L hw L.point.y hw.inputY k
  have hd := dialog_gateSlots_le L.dialogPort p (DialogLayout.fromPool_widths _ _ _ _)
  have hs := valueWalkSquare_gateSlots_le L hw hn
  have hn' := valueWalkNegate_gateSlots_le L hw
  have h1 := hx (-cx); have h2 := hy (-cy); have h3 := hx (3*cx); have h4 := hx cx
  simp only [valueWalkPointDialogGeneric, gateSlots_append]
  omega

theorem maskedPoint_gateSlots_le (c : Wire) (r : PointReg) (C : Point) :
    gateSlots (maskedPointConstant c r C) ≤ 1 + r.x.length + r.y.length := by
  have hf := maskedConstant_gateSlots_le c [r.finite] (pointFinite C).toNat
  have hx := maskedConstant_gateSlots_le c r.x (pointX C)
  have hy := maskedConstant_gateSlots_le c r.y (pointY C)
  simp only [maskedPointConstant, gateSlots_append]
  simp only [List.length_cons, List.length_nil] at hf
  omega

theorem valueWalkFinite_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) : gateSlots (valueWalkPointDialogFinite L C cx cy) ≤ 61000000 := by
  have hg := valueWalkGeneric_gateSlots_le L hw hn cx cy
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
  simp only [valueWalkPointDialogFinite, pointDialogCorners, pointInPlaceCorners, gateSlots_append, hf]
  omega

theorem normalizedValueWalk_gateSlots_le (C : Point) :
    gateSlots (normalizedValueWalk C) ≤ 61000000 := by
  rw [normalizedValueWalk, normalize_gateSlots]
  cases C with
  | zero => simp [valueWalk, Submissions.ValueWalk.program]
  | some hp => exact valueWalkFinite_gateSlots_le layout layout_widths layout_nodup _ _ _

end ECDSAAdd.Baselines
