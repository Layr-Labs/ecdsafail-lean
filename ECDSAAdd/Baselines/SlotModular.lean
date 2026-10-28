import ECDSAAdd.Baselines.SlotAlgebra

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem controlledMod_gateSlots_le (c : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) :
    gateSlots (controlledModAdd c L p) ≤ 56*n+35 ∧
    gateSlots (controlledModSub c L p) ≤ 86*n+65 := by
  have hm := modAddCore_gateSlots_le L.maskedCore p
  change gateSlots (modAddCore L.maskedCore p) ≤
    14 * L.mask.length + 14 * L.constant.length + 26 * L.low.length + 7 at hm
  rw [hw.mask, hw.core.constant, hw.core.low] at hm
  have hn := negRaw_gateSlots_le L p
  rw [hw.core.a, hw.core.constant] at hn
  have hc : gateSlots (copyRegister (some c) (L.a.take L.low.length) (L.mask.take L.low.length)) = n := by
    simp [hw.core.a, hw.core.low, hw.mask]
  have ha : gateSlots (controlledModAdd c L p) ≤ 56*n+35 := by
    simp only [controlledModAdd, gateSlots_append, hc]; omega
  refine ⟨ha, ?_⟩
  simp only [controlledModSub, gateSlots_append]; omega

theorem controlledUnary_gateSlots_le (c : Wire) (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) :
    gateSlots (controlledHalf c U p) ≤ 31*n+20 ∧
    gateSlots (controlledDouble c U p) ≤ 33*n+21 := by
  have hz : U.z.length = n+1 := by simp [ModUnaryLayout.z, hw.low]
  have hm := maskedConst_gateSlots_le U.flag U.constant U.z U.carry U.cin p
  have hm' := maskedConst_gateSlots_le c U.constant U.z U.carry U.cin p
  have hl := (maskedConst_gateSlots_le U.high (U.constant.take U.low.length) U.low
    (U.carry.take (U.low.length-1)) U.cin p).1
  have hs := shift_gateSlots c U.z
  have hc := compareLtConst_gateSlots_le (some c) U.low (U.constant.take U.low.length) U.carry U.cin U.flag ((p+1)/2)
  rw [hw.constant, hz] at hm hm'
  rw [hz] at hs
  simp only [List.length_take, hw.constant, hw.low, Nat.min_eq_left (Nat.le_succ n)] at hl hc
  simp only [controlledHalf, controlledDouble, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots, hw.low]
  constructor <;> omega

theorem replayCell_gateSlots_le (a sw su : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) :
    gateSlots (replayCell a sw su L p) ≤ 123*n+85 ∧
    gateSlots (replayUncell a sw su L p) ≤ 95*n+56 := by
  have hm := controlledMod_gateSlots_le su L n p hw
  have hu := controlledUnary_gateSlots_le a L.unary n p (L.unary_widths n hw)
  have hz : L.z.length = n+1 := by simp [ModInPlaceLayout.z, ModAddCoreLayout.z, hw.core.low]
  have hs : gateSlots (swapRegisters sw (L.z.take L.low.length) (L.a.take L.low.length)) = 3*n := by
    simp [hw.core.low, hw.core.a, hz]
  simp only [replayCell, replayUncell, gateSlots_append, hs]
  constructor <;> omega

end ECDSAAdd.Baselines
