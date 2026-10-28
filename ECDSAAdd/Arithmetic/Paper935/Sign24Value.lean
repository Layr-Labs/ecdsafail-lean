import ECDSAAdd.Arithmetic.Paper935.Sign24Cleanup

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def sign24Word : List Wire := List.range' 1 58

def sign24Carry (subtract : Bool) (j : Nat) (s : BasisState) : Bool :=
  foldBlockOverflow (sign24Cells subtract j false) (s 0)
    (((sign24Input j).map s).getD false) s

theorem sign24_forward_value (subtract : Bool) (j : Nat) (hj : j<3) (s : State) (m : List Bool)
    (ready : Sign24Ready j s.basis) :
    regValue ((sign24Cells subtract j false).map FoldCell.data)
      (run (sign24Forward subtract j) m s).basis=
    (regValue ((sign24Cells subtract j false).map FoldCell.data) s.basis+
      foldBlockLiteral (sign24Cells subtract j false) (s.basis 0)+
      (((sign24Input j).map s.basis).getD false).toNat)%2^(sign24Cells subtract j false).length := by
  have clean := sign24_forward_clean subtract j hj s.basis ready
  by_cases h : j<2
  · rw [sign24Forward,if_pos h]
    exact foldBlockSave_value 0 (sign24Top j) (sign24Saved subtract j) _ _
      (sign24_cells_geometry subtract j hj) (sign24_saved_mem subtract j h)
      (sign24_cells_top subtract j hj) (sign24_top_distinct j h) s m clean
  · rw [sign24Forward,if_neg h,foldBlock_run 0 _ _ true false
      (sign24_cells_geometry subtract j hj) s m clean]
    exact foldBlockModel_value 0 _ _ false (sign24_cells_geometry subtract j hj) s.basis

theorem sign24_forward_carry (subtract : Bool) (j : Nat) (hj : j<2) (s : State) (m : List Bool)
    (ready : Sign24Ready j s.basis) :
    (run (sign24Forward subtract j) m s).basis (59+j)=sign24Carry subtract j s.basis := by
  rw [sign24Forward,if_pos hj]
  simpa only [sign24Saved,if_pos rfl] using
    foldBlockSave_carries 0 (sign24Top j) (sign24Saved subtract j) _ _
      (sign24_cells_geometry subtract j (by omega)) (sign24_saved_mem subtract j hj)
      (sign24_cells_top subtract j (by omega)) (sign24_top_distinct j hj) s m
      (sign24_forward_clean subtract j (by omega) s.basis ready)
      (sign24Saved subtract j) (sign24_saved_mem subtract j hj)

private theorem word_split (subtract : Bool) (j : Nat) (hj : j<3) :
    sign24Word=List.range' 1 (sign24Starts[j]?.getD 0)++
      (sign24Cells subtract j false).map FoldCell.data++
      List.range' (1+sign24Starts[j]?.getD 0+sign24Sizes[j]?.getD 0)
        (58-(sign24Starts[j]?.getD 0+sign24Sizes[j]?.getD 0)) := by
  cases subtract <;> interval_cases j <;> decide

private theorem outside_frame (subtract : Bool) (j : Nat) (hj : j<3) (s : State) (m : List Bool)
    (ready : Sign24Ready j s.basis) (q : Wire) (hq : q<59)
    (outside : q<1+sign24Starts[j]?.getD 0 ∨
      1+sign24Starts[j]?.getD 0+sign24Sizes[j]?.getD 0≤q) :
    (run (sign24Forward subtract j) m s).basis q=s.basis q := by
  apply sign24_forward_frame subtract j hj s m ready
  intro mem
  have bounds := sign24_cells_bounds subtract j false q mem
  simp only [Bool.false_eq_true,if_false] at bounds
  dsimp only [Wire] at *
  omega

/-- Exact whole-word conservation for one physical block, including its
carry. The final block's discarded carry remains a mathematical Boolean. -/
theorem sign24_forward_conservation (subtract : Bool) (j : Nat) (hj : j<3) (s : State) (m : List Bool)
    (ready : Sign24Ready j s.basis) :
    regValue sign24Word (run (sign24Forward subtract j) m s).basis+
      2^(sign24Starts[j]?.getD 0+sign24Sizes[j]?.getD 0)*(sign24Carry subtract j s.basis).toNat=
    regValue sign24Word s.basis+2^(sign24Starts[j]?.getD 0)*
      (foldBlockLiteral (sign24Cells subtract j false) (s.basis 0)+
        (((sign24Input j).map s.basis).getD false).toNat) := by
  have lowSame : regValue (List.range' 1 (sign24Starts[j]?.getD 0))
      (run (sign24Forward subtract j) m s).basis=
      regValue (List.range' 1 (sign24Starts[j]?.getD 0)) s.basis := by
    apply regValue_congr
    intro q hq
    have part := sign24_partition j hj
    simp only [List.mem_range'] at hq
    apply outside_frame subtract j hj s m ready q (by dsimp only [Wire]; omega) (Or.inl (by dsimp only [Wire]; omega))
  have highSame : regValue (List.range' (1+sign24Starts[j]?.getD 0+sign24Sizes[j]?.getD 0)
      (58-(sign24Starts[j]?.getD 0+sign24Sizes[j]?.getD 0)))
      (run (sign24Forward subtract j) m s).basis=
      regValue (List.range' (1+sign24Starts[j]?.getD 0+sign24Sizes[j]?.getD 0)
        (58-(sign24Starts[j]?.getD 0+sign24Sizes[j]?.getD 0))) s.basis := by
    apply regValue_congr
    intro q hq
    have part := sign24_partition j hj
    simp only [List.mem_range'] at hq
    apply outside_frame subtract j hj s m ready q (by dsimp only [Wire]; omega) (Or.inr (by omega))
  have value := sign24_forward_value subtract j hj s m ready
  have conservation := foldBlockOverflow_value (sign24Cells subtract j false) (s.basis 0)
    (((sign24Input j).map s.basis).getD false) s.basis
  rw [←value] at conservation
  change _+_*(sign24Carry subtract j s.basis).toNat=_ at conservation
  have len : (sign24Cells subtract j false).length=sign24Sizes[j]?.getD 0 := by
    simp [sign24Cells]
  rw [word_split subtract j hj]
  simp only [regValue_append,lowSame,highSame,List.length_append,List.length_range',List.length_map,len,Nat.pow_add]
  rw [len] at conservation
  have weighted := congrArg (fun x => 2^(sign24Starts[j]?.getD 0)*x) conservation
  nlinarith only [weighted]

end ECDSAAdd.Arithmetic.Paper935
