import ECDSAAdd.Arithmetic.Paper935.HmrDataChecks
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulTemplateCopy
namespace ECDSAAdd.Arithmetic.Paper935

theorem rowMulCopy_placement (w : Nat → Wire) (b : Nat) : rowMulCopy w b =
    renameRecordedProgram w (relocateRecords b (rowMulCopy id 0)) := by
  unfold rowMulCopy
  simp only [renameRecordedProgram, relocateRecords, List.map_append]
  repeat' apply congrArg₂ List.append
  all_goals rfl

private theorem checked_wires : hmrCheckWires (fun q => decide (q < 820))
    (rowMulCopy id 0) = true := by decide +kernel

private theorem checked_gates : hmrGatesOnly (rowMulCopy id 0) = true := by decide +kernel

attribute [local irreducible] rowMulCopy

theorem rowMulCopy_support (w : Nat → Wire) (b : Nat) :
    recordedWires (rowMulCopy w b) ⊆ (Finset.range 820).image w := by
  rw [rowMulCopy_placement, renameRecorded_wires, relocateRecords_wires]
  apply Finset.image_subset_image
  intro q hq
  exact Finset.mem_range.mpr (of_decide_eq_true (hmrCheckWires_sound (fun q => decide (q < 820)) (rowMulCopy id 0) checked_wires q hq))

theorem rowMulCopy_gatesOnly (w : Nat → Wire) (b : Nat) : hmrGatesOnly (rowMulCopy w b) = true := by
  rw [rowMulCopy_placement, hmrGatesOnly_rename, hmrGatesOnly_relocate]
  exact checked_gates
end ECDSAAdd.Arithmetic.Paper935
