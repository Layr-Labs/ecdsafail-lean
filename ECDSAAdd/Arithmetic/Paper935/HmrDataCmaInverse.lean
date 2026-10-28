import ECDSAAdd.Arithmetic.Paper935.HmrDataChecks
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulTemplateCmaInverse
namespace ECDSAAdd.Arithmetic.Paper935

theorem rowMulCmaInverse_placement (w : Nat → Wire) (b : Nat) : rowMulCmaInverse w b =
    renameRecordedProgram w (relocateRecords b (rowMulCmaInverse id 0)) := by
  unfold rowMulCmaInverse
  simp only [renameRecordedProgram, relocateRecords, List.map_append]
  repeat' apply congrArg₂ List.append
  all_goals rfl

private theorem checked_wires : hmrCheckWires (fun q => decide (q < 820))
    (rowMulCmaInverse id 0) = true := by decide +kernel

private theorem checked_gates : hmrGatesOnly (rowMulCmaInverse id 0) = true := by decide +kernel

attribute [local irreducible] rowMulCmaInverse

theorem rowMulCmaInverse_support (w : Nat → Wire) (b : Nat) :
    recordedWires (rowMulCmaInverse w b) ⊆ (Finset.range 820).image w := by
  rw [rowMulCmaInverse_placement, renameRecorded_wires, relocateRecords_wires]
  apply Finset.image_subset_image
  intro q hq
  exact Finset.mem_range.mpr (of_decide_eq_true (hmrCheckWires_sound (fun q => decide (q < 820)) (rowMulCmaInverse id 0) checked_wires q hq))

theorem rowMulCmaInverse_gatesOnly (w : Nat → Wire) (b : Nat) : hmrGatesOnly (rowMulCmaInverse w b) = true := by
  rw [rowMulCmaInverse_placement, hmrGatesOnly_rename, hmrGatesOnly_relocate]
  exact checked_gates
end ECDSAAdd.Arithmetic.Paper935
