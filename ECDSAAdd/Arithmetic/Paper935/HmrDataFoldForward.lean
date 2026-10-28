import ECDSAAdd.Arithmetic.Paper935.HmrDataChecks
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulTemplateFoldForward
namespace ECDSAAdd.Arithmetic.Paper935

theorem rowMulFoldForward_placement (w : Nat → Wire) (b : Nat) : rowMulFoldForward w b =
    renameRecordedProgram w (relocateRecords b (rowMulFoldForward id 0)) := by
  unfold rowMulFoldForward
  simp only [renameRecordedProgram, relocateRecords, List.map_append]
  repeat' apply congrArg₂ List.append
  all_goals rfl

private theorem checked_wires : hmrCheckWires (fun q => decide (q < 820))
    (rowMulFoldForward id 0) = true := by decide +kernel

private theorem checked_gates : hmrGatesOnly (rowMulFoldForward id 0) = true := by decide +kernel

attribute [local irreducible] rowMulFoldForward

theorem rowMulFoldForward_support (w : Nat → Wire) (b : Nat) :
    recordedWires (rowMulFoldForward w b) ⊆ (Finset.range 820).image w := by
  rw [rowMulFoldForward_placement, renameRecorded_wires, relocateRecords_wires]
  apply Finset.image_subset_image
  intro q hq
  exact Finset.mem_range.mpr (of_decide_eq_true (hmrCheckWires_sound (fun q => decide (q < 820)) (rowMulFoldForward id 0) checked_wires q hq))

theorem rowMulFoldForward_gatesOnly (w : Nat → Wire) (b : Nat) : hmrGatesOnly (rowMulFoldForward w b) = true := by
  rw [rowMulFoldForward_placement, hmrGatesOnly_rename, hmrGatesOnly_relocate]
  exact checked_gates
end ECDSAAdd.Arithmetic.Paper935
