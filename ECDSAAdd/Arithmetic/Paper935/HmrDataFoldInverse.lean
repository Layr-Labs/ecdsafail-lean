import ECDSAAdd.Arithmetic.Paper935.HmrDataChecks
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulTemplateFoldInverse
namespace ECDSAAdd.Arithmetic.Paper935

theorem rowMulFoldInverse_placement (w : Nat → Wire) (b : Nat) : rowMulFoldInverse w b =
    renameRecordedProgram w (relocateRecords b (rowMulFoldInverse id 0)) := by
  unfold rowMulFoldInverse
  simp only [renameRecordedProgram, relocateRecords, List.map_append]
  repeat' apply congrArg₂ List.append
  all_goals rfl

private theorem checked_wires : hmrCheckWires (fun q => decide (q < 820))
    (rowMulFoldInverse id 0) = true := by decide +kernel

private theorem checked_gates : hmrGatesOnly (rowMulFoldInverse id 0) = true := by decide +kernel

attribute [local irreducible] rowMulFoldInverse

theorem rowMulFoldInverse_support (w : Nat → Wire) (b : Nat) :
    recordedWires (rowMulFoldInverse w b) ⊆ (Finset.range 820).image w := by
  rw [rowMulFoldInverse_placement, renameRecorded_wires, relocateRecords_wires]
  apply Finset.image_subset_image
  intro q hq
  exact Finset.mem_range.mpr (of_decide_eq_true (hmrCheckWires_sound (fun q => decide (q < 820)) (rowMulFoldInverse id 0) checked_wires q hq))

theorem rowMulFoldInverse_gatesOnly (w : Nat → Wire) (b : Nat) : hmrGatesOnly (rowMulFoldInverse w b) = true := by
  rw [rowMulFoldInverse_placement, hmrGatesOnly_rename, hmrGatesOnly_relocate]
  exact checked_gates
end ECDSAAdd.Arithmetic.Paper935
