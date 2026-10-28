import ECDSAAdd.Arithmetic.Paper935.Fold16Cleanup

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def fold16Word : List Wire := List.range' 1 58

def fold16Carry (subtract : Bool) (j : Nat) (s : BasisState) : Bool :=
  foldBlockOverflow (fold16Cells subtract j false) (s 0)
    (((fold16Input j).map s).getD false) s

theorem fold16_forward_value (subtract : Bool) (j : Nat) (hj : j<5) (s : State) (m : List Bool)
    (ready : Fold16Ready j s.basis) :
    regValue ((fold16Cells subtract j false).map FoldCell.data)
      (run (fold16Forward subtract j) m s).basis=
    (regValue ((fold16Cells subtract j false).map FoldCell.data) s.basis+
      foldBlockLiteral (fold16Cells subtract j false) (s.basis 0)+
      (((fold16Input j).map s.basis).getD false).toNat)%2^(fold16Cells subtract j false).length := by
  have clean := fold16_forward_clean subtract j hj s.basis ready
  by_cases h : j<4
  · rw [fold16Forward,if_pos h]
    exact foldBlockSave_value 0 (fold16Top j) (fold16Saved subtract j) _ _
      (fold16_cells_geometry subtract j hj) (fold16_saved_mem subtract j h)
      (fold16_cells_top subtract j hj) (fold16_top_distinct j h) s m clean
  · rw [fold16Forward,if_neg h,foldBlock_run 0 _ _ true false
      (fold16_cells_geometry subtract j hj) s m clean]
    exact foldBlockModel_value 0 _ _ false (fold16_cells_geometry subtract j hj) s.basis

theorem fold16_forward_carry (subtract : Bool) (j : Nat) (hj : j<4) (s : State) (m : List Bool)
    (ready : Fold16Ready j s.basis) :
    (run (fold16Forward subtract j) m s).basis (59+j)=fold16Carry subtract j s.basis := by
  rw [fold16Forward,if_pos hj]
  simpa only [fold16Saved,if_pos rfl] using
    foldBlockSave_carries 0 (fold16Top j) (fold16Saved subtract j) _ _
      (fold16_cells_geometry subtract j (by omega)) (fold16_saved_mem subtract j hj)
      (fold16_cells_top subtract j (by omega)) (fold16_top_distinct j hj) s m
      (fold16_forward_clean subtract j (by omega) s.basis ready)
      (fold16Saved subtract j) (fold16_saved_mem subtract j hj)

private theorem word_split (subtract : Bool) (j : Nat) (hj : j<5) :
    fold16Word=List.range' 1 (fold16Starts[j]?.getD 0)++
      (fold16Cells subtract j false).map FoldCell.data++
      List.range' (1+fold16Starts[j]?.getD 0+fold16Sizes[j]?.getD 0)
        (58-(fold16Starts[j]?.getD 0+fold16Sizes[j]?.getD 0)) := by
  cases subtract <;> interval_cases j <;> decide

private theorem outside_frame (subtract : Bool) (j : Nat) (hj : j<5) (s : State) (m : List Bool)
    (ready : Fold16Ready j s.basis) (q : Wire) (hq : q<59)
    (outside : q<1+fold16Starts[j]?.getD 0 ∨
      1+fold16Starts[j]?.getD 0+fold16Sizes[j]?.getD 0≤q) :
    (run (fold16Forward subtract j) m s).basis q=s.basis q := by
  apply fold16_forward_frame subtract j hj s m ready
  intro mem
  have bounds := fold16_cells_bounds subtract j false q mem
  simp only [Bool.false_eq_true,if_false] at bounds
  dsimp only [Wire] at *
  omega

/-- Exact whole-word conservation for one physical block, including its
carry. The final block's discarded carry remains a mathematical Boolean. -/
theorem fold16_forward_conservation (subtract : Bool) (j : Nat) (hj : j<5) (s : State) (m : List Bool)
    (ready : Fold16Ready j s.basis) :
    regValue fold16Word (run (fold16Forward subtract j) m s).basis+
      2^(fold16Starts[j]?.getD 0+fold16Sizes[j]?.getD 0)*(fold16Carry subtract j s.basis).toNat=
    regValue fold16Word s.basis+2^(fold16Starts[j]?.getD 0)*
      (foldBlockLiteral (fold16Cells subtract j false) (s.basis 0)+
        (((fold16Input j).map s.basis).getD false).toNat) := by
  have lowSame : regValue (List.range' 1 (fold16Starts[j]?.getD 0))
      (run (fold16Forward subtract j) m s).basis=
      regValue (List.range' 1 (fold16Starts[j]?.getD 0)) s.basis := by
    apply regValue_congr
    intro q hq
    have part := fold16_partition j hj
    simp only [List.mem_range'] at hq
    apply outside_frame subtract j hj s m ready q (by dsimp only [Wire]; omega) (Or.inl (by dsimp only [Wire]; omega))
  have highSame : regValue (List.range' (1+fold16Starts[j]?.getD 0+fold16Sizes[j]?.getD 0)
      (58-(fold16Starts[j]?.getD 0+fold16Sizes[j]?.getD 0)))
      (run (fold16Forward subtract j) m s).basis=
      regValue (List.range' (1+fold16Starts[j]?.getD 0+fold16Sizes[j]?.getD 0)
        (58-(fold16Starts[j]?.getD 0+fold16Sizes[j]?.getD 0))) s.basis := by
    apply regValue_congr
    intro q hq
    have part := fold16_partition j hj
    simp only [List.mem_range'] at hq
    apply outside_frame subtract j hj s m ready q (by dsimp only [Wire]; omega) (Or.inr (by omega))
  have value := fold16_forward_value subtract j hj s m ready
  have conservation := foldBlockOverflow_value (fold16Cells subtract j false) (s.basis 0)
    (((fold16Input j).map s.basis).getD false) s.basis
  rw [←value] at conservation
  change _+_*(fold16Carry subtract j s.basis).toNat=_ at conservation
  have len : (fold16Cells subtract j false).length=fold16Sizes[j]?.getD 0 := by
    simp [fold16Cells]
  rw [word_split subtract j hj]
  simp only [regValue_append,lowSame,highSame,List.length_append,List.length_range',List.length_map,len,Nat.pow_add]
  rw [len] at conservation
  have weighted := congrArg (fun x => 2^(fold16Starts[j]?.getD 0)*x) conservation
  nlinarith only [weighted]

end ECDSAAdd.Arithmetic.Paper935
