import ECDSAAdd.Arithmetic.Paper935.HmrSupportList
import ECDSAAdd.Arithmetic.Paper935.HmrSourceCallPorts
namespace ECDSAAdd.Arithmetic.Paper935
attribute [local irreducible] s2HmrSourceLayout placedRowFold placedMagnitude
  fusedRowFoldSource fusedMagnitudeLift
private def foldMap := fusedPlacementMap (fusedFoldPlacement
  s2HmrSourceLayout.row.payload s2HmrSourceLayout.y s2HmrSourceLayout.anc)
private def liftMap := fusedPlacementMap
  (s2HmrSourceLayout.row.sign :: s2HmrSourceLayout.row.payload ++ s2HmrSourceLayout.anc)
private theorem foldMap_checked : ∀q∈Finset.range 537,
    foldMap q ∈ s2SupportList := by decide +kernel
private theorem liftMap_checked : ∀q∈Finset.range 305,
    liftMap q ∈ s2SupportList := by decide +kernel

theorem s2Unpark_support_checked :
    recordedWires s2HmrSourceUnpark ⊆ s2HmrSourceLayout.support := by
  unfold s2HmrSourceUnpark
  rw [embedRecorded_wires,wires_append]
  apply Finset.union_subset
  · unfold placedRowFold
    rw [renameProgram_support]
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact (s2SupportList_mem _).mp (foldMap_checked i ((fusedRowFoldSource_resources true).1 hi))
  · unfold placedMagnitude
    rw [renameProgram_support]
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact (s2SupportList_mem _).mp (liftMap_checked i (fusedMagnitudeLift_support true hi))
end ECDSAAdd.Arithmetic.Paper935
