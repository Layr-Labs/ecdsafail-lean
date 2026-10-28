import ECDSAAdd.Arithmetic.Paper935.HmrDataChecks
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulTemplateHalveForward
namespace ECDSAAdd.Arithmetic.Paper935

theorem rowMulHalveForward_placement (w : Nat → Wire) (b : Nat) : rowMulHalveForward w b =
    renameRecordedProgram w (relocateRecords b (rowMulHalveForward id 0)) := by
  unfold rowMulHalveForward
  simp only [renameRecordedProgram, relocateRecords, List.map_append]
  repeat' apply congrArg₂ List.append
  all_goals rfl

private theorem checked_wires : hmrCheckWires (fun q => decide (q < 820))
    (rowMulHalveForward id 0) = true := by decide +kernel

private theorem checked_gates : hmrGatesOnly (rowMulHalveForward id 0) = true := by decide +kernel

attribute [local irreducible] rowMulHalveForward

theorem rowMulHalveForward_support (w : Nat → Wire) (b : Nat) :
    recordedWires (rowMulHalveForward w b) ⊆ (Finset.range 820).image w := by
  rw [rowMulHalveForward_placement, renameRecorded_wires, relocateRecords_wires]
  apply Finset.image_subset_image
  intro q hq
  exact Finset.mem_range.mpr (of_decide_eq_true (hmrCheckWires_sound (fun q => decide (q < 820)) (rowMulHalveForward id 0) checked_wires q hq))

theorem rowMulHalveForward_gatesOnly (w : Nat → Wire) (b : Nat) : hmrGatesOnly (rowMulHalveForward w b) = true := by
  rw [rowMulHalveForward_placement, hmrGatesOnly_rename, hmrGatesOnly_relocate]
  exact checked_gates
end ECDSAAdd.Arithmetic.Paper935
