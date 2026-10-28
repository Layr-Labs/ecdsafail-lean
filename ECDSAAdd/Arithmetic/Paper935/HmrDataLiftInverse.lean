import ECDSAAdd.Arithmetic.Paper935.HmrDataChecks
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulTemplateLiftInverse
namespace ECDSAAdd.Arithmetic.Paper935

theorem rowMulLiftInverse_placement (w : Nat → Wire) (b : Nat) : rowMulLiftInverse w b =
    renameRecordedProgram w (relocateRecords b (rowMulLiftInverse id 0)) := by
  unfold rowMulLiftInverse
  simp only [renameRecordedProgram, relocateRecords, List.map_append]
  repeat' apply congrArg₂ List.append
  all_goals rfl

private theorem checked_wires : hmrCheckWires (fun q => decide (q < 820))
    (rowMulLiftInverse id 0) = true := by decide +kernel

private theorem checked_gates : hmrGatesOnly (rowMulLiftInverse id 0) = true := by decide +kernel

attribute [local irreducible] rowMulLiftInverse

theorem rowMulLiftInverse_support (w : Nat → Wire) (b : Nat) :
    recordedWires (rowMulLiftInverse w b) ⊆ (Finset.range 820).image w := by
  rw [rowMulLiftInverse_placement, renameRecorded_wires, relocateRecords_wires]
  apply Finset.image_subset_image
  intro q hq
  exact Finset.mem_range.mpr (of_decide_eq_true (hmrCheckWires_sound (fun q => decide (q < 820)) (rowMulLiftInverse id 0) checked_wires q hq))

theorem rowMulLiftInverse_gatesOnly (w : Nat → Wire) (b : Nat) : hmrGatesOnly (rowMulLiftInverse w b) = true := by
  rw [rowMulLiftInverse_placement, hmrGatesOnly_rename, hmrGatesOnly_relocate]
  exact checked_gates
end ECDSAAdd.Arithmetic.Paper935
