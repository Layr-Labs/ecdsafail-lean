import ECDSAAdd.Arithmetic.Paper935.HmrDataCopy
import ECDSAAdd.Arithmetic.Paper935.HmrDataCmaForward
import ECDSAAdd.Arithmetic.Paper935.HmrDataCmaInverse
import ECDSAAdd.Arithmetic.Paper935.HmrDataFoldForward
import ECDSAAdd.Arithmetic.Paper935.HmrDataFoldInverse
import ECDSAAdd.Arithmetic.Paper935.HmrDataHalveForward
import ECDSAAdd.Arithmetic.Paper935.HmrDataHalveInverse
import ECDSAAdd.Arithmetic.Paper935.HmrDataLiftForward
import ECDSAAdd.Arithmetic.Paper935.HmrDataLiftInverse
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulSourcePrograms
namespace ECDSAAdd.Arithmetic.Paper935
attribute [local irreducible] rowMulCopy rowMulCmaForward rowMulCmaInverse
  rowMulFoldForward rowMulFoldInverse rowMulHalveForward rowMulHalveInverse
  rowMulLiftForward rowMulLiftInverse

theorem rowMulInstantiate_support (ports : Array Wire) (start : Nat) (u : RowMulTemplateUse) :
    recordedWires (rowMulInstantiate ports start u) ⊆
      (Finset.range 820).image (rowMulPort ports u.control) := by
  unfold rowMulInstantiate
  split
  · exact rowMulCmaForward_support _ _
  · exact rowMulCmaInverse_support _ _
  · exact rowMulCopy_support _ _
  · exact rowMulFoldForward_support _ _
  · exact rowMulFoldInverse_support _ _
  · exact rowMulHalveForward_support _ _
  · exact rowMulHalveInverse_support _ _
  · exact rowMulLiftForward_support _ _
  · exact rowMulLiftInverse_support _ _
  · simp [recordedWires]

theorem rowMulInstantiate_gatesOnly (ports : Array Wire) (start : Nat) (u : RowMulTemplateUse) :
    hmrGatesOnly (rowMulInstantiate ports start u) = true := by
  unfold rowMulInstantiate
  split
  · exact rowMulCmaForward_gatesOnly _ _
  · exact rowMulCmaInverse_gatesOnly _ _
  · exact rowMulCopy_gatesOnly _ _
  · exact rowMulFoldForward_gatesOnly _ _
  · exact rowMulFoldInverse_gatesOnly _ _
  · exact rowMulHalveForward_gatesOnly _ _
  · exact rowMulHalveInverse_gatesOnly _ _
  · exact rowMulLiftForward_gatesOnly _ _
  · exact rowMulLiftInverse_gatesOnly _ _
  · rfl

theorem rowMulUses_gatesOnly (ports : Array Wire) (start : Nat) (uses : List RowMulTemplateUse) :
    hmrGatesOnly (uses.flatMap (rowMulInstantiate ports start)) = true := by
  induction uses with
  | nil => rfl
  | cons u us ih =>
    simp only [List.flatMap_cons, hmrGatesOnly, List.all_append]
    simp only [Bool.and_eq_true]
    exact ⟨rowMulInstantiate_gatesOnly _ _ _, ih⟩

theorem rowMulUses_support (ports : Array Wire) (start : Nat) (uses : List RowMulTemplateUse)
    (S : Finset Wire)
    (ports_ok : ∀ q ∈ Finset.range 820, rowMulPort ports 0 q ∈ S)
    (controls_ok : ∀ u ∈ uses, u.control ∈ S) :
    recordedWires (uses.flatMap (rowMulInstantiate ports start)) ⊆ S := by
  induction uses with
  | nil => simp [recordedWires]
  | cons u us ih =>
    rw [List.flatMap_cons, recordedWires_append]
    apply Finset.union_subset
    · intro q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (rowMulInstantiate_support ports start u hq)
      by_cases h : i = 819
      · simpa [rowMulPort,h] using controls_ok u (by simp)
      · simpa [rowMulPort,h] using ports_ok i hi
    · exact ih (fun v hv => controls_ok v (List.mem_cons_of_mem _ hv))

end ECDSAAdd.Arithmetic.Paper935
