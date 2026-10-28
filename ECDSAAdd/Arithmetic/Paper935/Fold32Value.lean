import ECDSAAdd.Arithmetic.Paper935.Fold32Cleanup

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def fold32Word : List Wire := List.range' 1 257

def fold32Carry (bits : Nat → Bool) (j : Nat) (s : BasisState) : Bool :=
  foldBlockOverflow (fold32Cells bits j false) (s 0)
    (((fold32Input j).map s).getD false) s

theorem fold32_forward_value (bits : Nat → Bool) (j : Nat) (hj : j<10) (s : State) (m : List Bool)
    (ready : Fold32Ready j s.basis) :
    regValue ((fold32Cells bits j false).map FoldCell.data)
      (run (fold32Forward bits j) m s).basis=
    (regValue ((fold32Cells bits j false).map FoldCell.data) s.basis+
      foldBlockLiteral (fold32Cells bits j false) (s.basis 0)+
      (((fold32Input j).map s.basis).getD false).toNat)%2^(fold32Cells bits j false).length := by
  have clean := fold32_forward_clean bits j hj s.basis ready
  by_cases h : j<9
  · rw [fold32Forward,if_pos h]
    exact foldBlockSave_value 0 (fold32Top j) (fold32Saved bits j) _ _
      (fold32_cells_geometry bits j hj) (fold32_saved_mem bits j h)
      (fold32_cells_top bits j hj) (fold32_top_distinct j h) s m clean
  · rw [fold32Forward,if_neg h,foldBlock_run 0 _ _ true false
      (fold32_cells_geometry bits j hj) s m clean]
    exact foldBlockModel_value 0 _ _ false (fold32_cells_geometry bits j hj) s.basis

theorem fold32_forward_carry (bits : Nat → Bool) (j : Nat) (hj : j<9) (s : State) (m : List Bool)
    (ready : Fold32Ready j s.basis) :
    (run (fold32Forward bits j) m s).basis (258+j)=fold32Carry bits j s.basis := by
  rw [fold32Forward,if_pos hj]
  simpa only [fold32Saved,if_pos rfl] using
    foldBlockSave_carries 0 (fold32Top j) (fold32Saved bits j) _ _
      (fold32_cells_geometry bits j (by omega)) (fold32_saved_mem bits j hj)
      (fold32_cells_top bits j (by omega)) (fold32_top_distinct j hj) s m
      (fold32_forward_clean bits j (by omega) s.basis ready)
      (fold32Saved bits j) (fold32_saved_mem bits j hj)

private theorem word_split (bits : Nat → Bool) (j : Nat) (hj : j<10) :
    fold32Word=List.range' 1 (fold32Starts[j]?.getD 0)++
      (fold32Cells bits j false).map FoldCell.data++
      List.range' (1+fold32Starts[j]?.getD 0+fold32Sizes[j]?.getD 0)
        (257-(fold32Starts[j]?.getD 0+fold32Sizes[j]?.getD 0)) := by
  simp only [fold32Cells,List.map_map,Function.comp_def]
  interval_cases j <;> decide +kernel

private theorem outside_frame (bits : Nat → Bool) (j : Nat) (hj : j<10) (s : State) (m : List Bool)
    (ready : Fold32Ready j s.basis) (q : Wire) (hq : q<258)
    (outside : q<1+fold32Starts[j]?.getD 0 ∨
      1+fold32Starts[j]?.getD 0+fold32Sizes[j]?.getD 0≤q) :
    (run (fold32Forward bits j) m s).basis q=s.basis q := by
  apply fold32_forward_frame bits j hj s m ready
  intro mem
  have bounds := fold32_cells_bounds bits j false q mem
  simp only [Bool.false_eq_true,if_false] at bounds
  dsimp only [Wire] at *
  omega

/-- Exact whole-word conservation for one physical block, including its
carry. The final block's discarded carry remains a mathematical Boolean. -/
theorem fold32_forward_conservation (bits : Nat → Bool) (j : Nat) (hj : j<10) (s : State) (m : List Bool)
    (ready : Fold32Ready j s.basis) :
    regValue fold32Word (run (fold32Forward bits j) m s).basis+
      2^(fold32Starts[j]?.getD 0+fold32Sizes[j]?.getD 0)*(fold32Carry bits j s.basis).toNat=
    regValue fold32Word s.basis+2^(fold32Starts[j]?.getD 0)*
      (foldBlockLiteral (fold32Cells bits j false) (s.basis 0)+
        (((fold32Input j).map s.basis).getD false).toNat) := by
  have lowSame : regValue (List.range' 1 (fold32Starts[j]?.getD 0))
      (run (fold32Forward bits j) m s).basis=
      regValue (List.range' 1 (fold32Starts[j]?.getD 0)) s.basis := by
    apply regValue_congr
    intro q hq
    have part := fold32_partition j hj
    simp only [List.mem_range'] at hq
    apply outside_frame bits j hj s m ready q (by dsimp only [Wire]; omega) (Or.inl (by dsimp only [Wire]; omega))
  have highSame : regValue (List.range' (1+fold32Starts[j]?.getD 0+fold32Sizes[j]?.getD 0)
      (257-(fold32Starts[j]?.getD 0+fold32Sizes[j]?.getD 0)))
      (run (fold32Forward bits j) m s).basis=
      regValue (List.range' (1+fold32Starts[j]?.getD 0+fold32Sizes[j]?.getD 0)
        (257-(fold32Starts[j]?.getD 0+fold32Sizes[j]?.getD 0))) s.basis := by
    apply regValue_congr
    intro q hq
    have part := fold32_partition j hj
    simp only [List.mem_range'] at hq
    apply outside_frame bits j hj s m ready q (by dsimp only [Wire]; omega) (Or.inr (by omega))
  have value := fold32_forward_value bits j hj s m ready
  have conservation := foldBlockOverflow_value (fold32Cells bits j false) (s.basis 0)
    (((fold32Input j).map s.basis).getD false) s.basis
  rw [←value] at conservation
  change _+_*(fold32Carry bits j s.basis).toNat=_ at conservation
  have len : (fold32Cells bits j false).length=fold32Sizes[j]?.getD 0 := by
    simp [fold32Cells]
  rw [word_split bits j hj]
  simp only [regValue_append,lowSame,highSame,List.length_append,List.length_range',List.length_map,len,Nat.pow_add]
  rw [len] at conservation
  have weighted := congrArg (fun x => 2^(fold32Starts[j]?.getD 0)*x) conservation
  nlinarith only [weighted]

end ECDSAAdd.Arithmetic.Paper935
