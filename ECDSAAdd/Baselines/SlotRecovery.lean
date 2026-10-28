import ECDSAAdd.Baselines.SlotMapped

namespace ECDSAAdd.Baselines
open Arithmetic Challenge Secp256k1

theorem recoveryConstant_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths)
    (r : List Wire) (hr : r.length = 256) (k : Fp) :
    gateSlots (pointDialogConstantAdd L r k) ≤ 18000 := by
  have hl := L.recoveryConstant_widths hw r hr
  have hp := canonicalMod_gateSlots_le (L.recoveryConstant r) 256 SquareReduction.c p hl
  have hm := maskedConstant_gateSlots_le L.core.generic (L.recoveryConstant r).src k.val
  rw [hl.src] at hm
  simp only [pointDialogConstantAdd, pointRecoveryConstantAdd, compactRecoveryConstant, gateSlots_append]
  omega

theorem recoveryReflection_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    gateSlots (pointRecoveryReflection L) ≤ 4608 := by
  have hm := maskedConstant_gateSlots_le L.core.generic L.recoveryNegate.word (2^L.recoveryNegate.word.length-1)
  have ha := mappedConst_gateSlots_le (some L.core.generic) L.recoveryNegate.word L.recoveryNegate.carries L.recoveryNegate.cin p
  have hl : L.recoveryNegate.word.length = 256 := hw.inputX
  rw [hl] at hm ha
  simp only [pointRecoveryReflection, CompactRecoveryNegateLayout.reflection,
    CompactRecoveryNegateLayout.complement, CompactRecoveryNegateLayout.add, gateSlots_append]
  -- The exponent is only a classical mask argument and has already been bounded.
  rw [hl]
  omega

theorem recoveryStage_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (pointRecoveryStage L cx cy) ≤ 40608 := by
  have hr := recoveryReflection_gateSlots_le L hw
  have hx := recoveryConstant_gateSlots_le L hw L.point.x hw.inputX (cx+1)
  have hy := recoveryConstant_gateSlots_le L hw L.point.y hw.inputY (-cy)
  simp only [pointRecoveryStage, gateSlots_append]; omega

end ECDSAAdd.Baselines
