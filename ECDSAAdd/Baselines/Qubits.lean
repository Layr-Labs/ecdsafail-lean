import ECDSAAdd.Baselines.Correctness

namespace ECDSAAdd.Baselines
open Arithmetic Secp256k1
attribute [local irreducible] valueWalkPointDialogFinite pointCompressedDialogFinite wires

theorem point_wires : PointAddLayout.pointWires layout.point = List.range' 1 513 := by
  have mr (a n : Nat) : (List.range n).map (· + a) = List.range' a n := by
    simpa only [Nat.add_comm] using (List.range'_eq_map_range (s := a) (n := n)).symm
  simp only [layout_point, PointAddLayout.pointWires, Challenge.point, mr]
  change List.range' 1 257 ++ List.range' 258 256 = List.range' 1 513
  exact List.range'_append_1

theorem io_partition (w : Wire) (h : w ∈ Challenge.ioWires) :
    w ∈ PointAddLayout.pointWires layout.point ∨ w = layout.control := by
  rw [point_wires]
  have hw : w < 514 := Finset.mem_range.mp h
  by_cases hz : w = 0
  · exact Or.inr hz
  · left
    apply List.mem_range'_1.mpr
    exact ⟨Nat.pos_of_ne_zero hz, hw⟩

theorem io_subset_sites :
    Challenge.ioWires ⊆ (CompressedPointDialog.sites layout).toFinset := by
  intro w hw
  have h := io_partition w hw
  simp only [CompressedPointDialog.sites, CompressedPointSquare.residents,
    List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil]
  rcases h with hp | hc
  · exact Or.inl (Or.inl (Or.inl hp))
  · exact Or.inl (Or.inl (Or.inr (Or.inl hc)))

theorem io_subset_dialog :
    Challenge.ioWires ⊆ layout.dialogUsedWires.toFinset := by
  intro w hw
  have h := io_partition w hw
  simp only [ControlledPointLayout.dialogUsedWires,
    List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil]
  rcases h with hp | hc
  · exact Or.inl (Or.inl (Or.inl hp))
  · exact Or.inl (Or.inl (Or.inr (Or.inl hc)))

theorem skywalk_qubits (C : Point) : Challenge.qubits (skywalk C) ≤ 1899 := by
  cases C with
  | zero =>
    change Challenge.qubits [] ≤ 1899
    rw [Challenge.qubits_empty]
    decide
  | @some cx cy hc =>
    have support := CompressedPointDialog.finite_support layout layout_widths layout_nodup (.some hc) cx cy
    have card := Finset.card_le_card (Finset.union_subset io_subset_sites support)
    have length : (CompressedPointDialog.sites layout).length = 1899 := by
      rw [CompressedPointDialog.sites, List.length_append,
        CompressedPointSquare.residents_length layout layout_widths,
        CompressedPointSquare.sharedPool_length]
    exact card.trans ((List.toFinset_card_le _).trans_eq length)

theorem valueWalk_qubits (C : Point) : Challenge.qubits (valueWalk C) ≤ 3134 := by
  cases C with
  | zero =>
    change Challenge.qubits [] ≤ 3134
    rw [Challenge.qubits_empty]
    decide
  | @some cx cy hc =>
    change (Challenge.ioWires ∪ wires (valueWalkPointDialogFinite layout (.some hc) _ _)).card ≤ 3134
    rw [valueWalkPointDialogFinite_wires layout layout_widths layout_nodup,
      Finset.union_eq_right.mpr io_subset_dialog,
      List.toFinset_card_of_nodup (layout.dialogUsed_nodup layout_nodup)]
    simp only [ControlledPointLayout.dialogUsedWires, List.length_append,
      PointAddLayout.pointWires, ControlledPointLayout.inPlaceFlags, List.length_cons,
      List.length_nil, show layout.point.x.length = 256 from layout_widths.inputX,
      show layout.point.y.length = 256 from layout_widths.inputY,
      ControlledPointLayout.dialogPool_length layout layout_widths]
    decide

end ECDSAAdd.Baselines
