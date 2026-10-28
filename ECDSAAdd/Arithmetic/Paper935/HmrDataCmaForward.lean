import ECDSAAdd.Arithmetic.Paper935.HmrDataChecks
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulTemplateCmaForward
namespace ECDSAAdd.Arithmetic.Paper935

theorem rowMulCmaForward_placement (w : Nat → Wire) (b : Nat) : rowMulCmaForward w b =
    renameRecordedProgram w (relocateRecords b (rowMulCmaForward id 0)) := by
  unfold rowMulCmaForward
  simp only [renameRecordedProgram, relocateRecords, List.map_append]
  repeat' apply congrArg₂ List.append
  all_goals rfl

private theorem checked_wires : hmrCheckWires (fun q => decide (q < 820))
    (rowMulCmaForward id 0) = true := by decide +kernel

private theorem checked_gates : hmrGatesOnly (rowMulCmaForward id 0) = true := by decide +kernel

attribute [local irreducible] rowMulCmaForward

theorem rowMulCmaForward_support (w : Nat → Wire) (b : Nat) :
    recordedWires (rowMulCmaForward w b) ⊆ (Finset.range 820).image w := by
  rw [rowMulCmaForward_placement, renameRecorded_wires, relocateRecords_wires]
  apply Finset.image_subset_image
  intro q hq
  exact Finset.mem_range.mpr (of_decide_eq_true (hmrCheckWires_sound (fun q => decide (q < 820)) (rowMulCmaForward id 0) checked_wires q hq))

theorem rowMulCmaForward_gatesOnly (w : Nat → Wire) (b : Nat) : hmrGatesOnly (rowMulCmaForward w b) = true := by
  rw [rowMulCmaForward_placement, hmrGatesOnly_rename, hmrGatesOnly_relocate]
  exact checked_gates
end ECDSAAdd.Arithmetic.Paper935
