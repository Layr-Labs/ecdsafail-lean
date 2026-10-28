import ECDSAAdd.Arithmetic.Paper935.HmrDataChecks
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulTemplateLiftForward
namespace ECDSAAdd.Arithmetic.Paper935

theorem rowMulLiftForward_placement (w : Nat → Wire) (b : Nat) : rowMulLiftForward w b =
    renameRecordedProgram w (relocateRecords b (rowMulLiftForward id 0)) := by
  unfold rowMulLiftForward
  simp only [renameRecordedProgram, relocateRecords, List.map_append]
  repeat' apply congrArg₂ List.append
  all_goals rfl

private theorem checked_wires : hmrCheckWires (fun q => decide (q < 820))
    (rowMulLiftForward id 0) = true := by decide +kernel

private theorem checked_gates : hmrGatesOnly (rowMulLiftForward id 0) = true := by decide +kernel

attribute [local irreducible] rowMulLiftForward

theorem rowMulLiftForward_support (w : Nat → Wire) (b : Nat) :
    recordedWires (rowMulLiftForward w b) ⊆ (Finset.range 820).image w := by
  rw [rowMulLiftForward_placement, renameRecorded_wires, relocateRecords_wires]
  apply Finset.image_subset_image
  intro q hq
  exact Finset.mem_range.mpr (of_decide_eq_true (hmrCheckWires_sound (fun q => decide (q < 820)) (rowMulLiftForward id 0) checked_wires q hq))

theorem rowMulLiftForward_gatesOnly (w : Nat → Wire) (b : Nat) : hmrGatesOnly (rowMulLiftForward w b) = true := by
  rw [rowMulLiftForward_placement, hmrGatesOnly_rename, hmrGatesOnly_relocate]
  exact checked_gates
end ECDSAAdd.Arithmetic.Paper935
