import ECDSAAdd.Baselines.SlotField

namespace ECDSAAdd.Baselines
open Arithmetic Challenge MappedCompressed
attribute [local irreducible] renameProgram MappedCompressed.controlled NativeFirstDirect.forward NativeFirstKnown.inverse
  compressedCompactForward compressedCompactReverse MappedCompressed.selectedFieldSegment
  MappedCompressed.kernel ZeroSeededConstantCompare.program maskedConstant

theorem zeroCompare_gateSlots_le (xs cs : List Wire) (c t : Wire) :
    gateSlots (ZeroSeededConstantCompare.program xs cs c t) ≤ 18*xs.length+4 := by
  cases xs with
  | nil => simp [ZeroSeededConstantCompare.program]
  | cons x xs =>
    cases xs with
    | nil => simp [ZeroSeededConstantCompare.program,ZeroSeededConstantCompare.prepare,gateSlots_cons,instructionSlots]
    | cons y ys =>
      cases cs with
      | nil => simp [ZeroSeededConstantCompare.program]
      | cons d ds =>
        have h := compareConstant_gateSlots_le (y::ys) ds d t 0
        simp only [ZeroSeededConstantCompare.program,ZeroSeededConstantCompare.prepare,
          ZeroSeededConstantCompare.release,gateSlots_append,gateSlots_cons,gateSlots_nil,
          instructionSlots,List.length_cons] at *; omega

theorem compressedKernel_gateSlots_le (divide : Bool) :
    gateSlots (MappedCompressed.kernel divide) ≤ 20500000 := by
  have hn := nativeFirst_gateSlots_le MappedCompressed.base
  have hi := compactLoops_gateSlots_le MappedCompressed.base 1 511 (by omega)
  have hf := fieldSegment_gateSlots_le divide
  have hc : gateSlots (skywalkArithmeticClear MappedCompressed.base) = 3 := rfl
  rw [MappedCompressed.kernel]
  simp only [gateSlots_append, hc]
  omega

theorem compressedControlled_gateSlots_le (divide : Bool) :
    gateSlots (MappedCompressed.controlled divide) ≤ 20600000 := by
  have hk := compressedKernel_gateSlots_le divide
  have hz := zeroCompare_gateSlots_le (wireBlock MappedCompressed.base 770 256)
    (wireBlock MappedCompressed.base 0 255) (MappedCompressed.base 2313) (MappedCompressed.base 2411)
  have hm := maskedConstant_gateSlots_le (MappedCompressed.base 2411) (wireBlock MappedCompressed.base 770 256) 1
  simp only [wireBlock_length] at hz hm
  simp only [MappedCompressed.controlled,directZeroControlled,directZeroDivisorEnter,directZeroDivisorLeave,
    gateSlots_append]; omega

theorem pointCompressedArithmetic_gateSlots_le (L : ControlledPointLayout) (multiply : Bool) :
    gateSlots (pointCompressedArithmetic L multiply) ≤ 20600000 := by
  simpa only [pointCompressedArithmetic,rename_gateSlots] using compressedControlled_gateSlots_le (!multiply)

end ECDSAAdd.Baselines
