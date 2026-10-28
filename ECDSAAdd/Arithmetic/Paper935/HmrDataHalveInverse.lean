import ECDSAAdd.Arithmetic.Paper935.HmrDataChecks
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulTemplateHalveInverse
namespace ECDSAAdd.Arithmetic.Paper935

theorem rowMulHalveInverse_placement (w : Nat → Wire) (b : Nat) : rowMulHalveInverse w b =
    renameRecordedProgram w (relocateRecords b (rowMulHalveInverse id 0)) := by
  unfold rowMulHalveInverse
  simp only [renameRecordedProgram, relocateRecords, List.map_append]
  repeat' apply congrArg₂ List.append
  all_goals rfl

private theorem checked_wires : hmrCheckWires (fun q => decide (q < 820))
    (rowMulHalveInverse id 0) = true := by decide +kernel

private theorem checked_gates : hmrGatesOnly (rowMulHalveInverse id 0) = true := by decide +kernel

attribute [local irreducible] rowMulHalveInverse

theorem rowMulHalveInverse_support (w : Nat → Wire) (b : Nat) :
    recordedWires (rowMulHalveInverse w b) ⊆ (Finset.range 820).image w := by
  rw [rowMulHalveInverse_placement, renameRecorded_wires, relocateRecords_wires]
  apply Finset.image_subset_image
  intro q hq
  exact Finset.mem_range.mpr (of_decide_eq_true (hmrCheckWires_sound (fun q => decide (q < 820)) (rowMulHalveInverse id 0) checked_wires q hq))

theorem rowMulHalveInverse_gatesOnly (w : Nat → Wire) (b : Nat) : hmrGatesOnly (rowMulHalveInverse w b) = true := by
  rw [rowMulHalveInverse_placement, hmrGatesOnly_rename, hmrGatesOnly_relocate]
  exact checked_gates
end ECDSAAdd.Arithmetic.Paper935
