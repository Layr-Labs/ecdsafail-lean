import ECDSAAdd.Arithmetic.Paper935.Lift24Cleanup

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def lift24Word : List Wire := List.range' 1 58

def lift24Carry (subtract : Bool) (j : Nat) (s : BasisState) : Bool :=
  foldBlockOverflow (lift24Cells subtract j false) (s 0)
    (((lift24Input j).map s).getD false) s

theorem lift24_forward_value (subtract : Bool) (j : Nat) (hj : j<3) (s : State) (m : List Bool)
    (ready : Lift24Ready j s.basis) :
    regValue ((lift24Cells subtract j false).map FoldCell.data)
      (run (lift24Forward subtract j) m s).basis=
    (regValue ((lift24Cells subtract j false).map FoldCell.data) s.basis+
      foldBlockLiteral (lift24Cells subtract j false) (s.basis 0)+
      (((lift24Input j).map s.basis).getD false).toNat)%2^(lift24Cells subtract j false).length := by
  have clean := lift24_forward_clean subtract j hj s.basis ready
  by_cases h : j<2
  · rw [lift24Forward,if_pos h]
    exact foldBlockSave_value 0 (lift24Top j) (lift24Saved subtract j) _ _
      (lift24_cells_geometry subtract j hj) (lift24_saved_mem subtract j h)
      (lift24_cells_top subtract j hj) (lift24_top_distinct j h) s m clean
  · rw [lift24Forward,if_neg h,foldBlock_run 0 _ _ true false
      (lift24_cells_geometry subtract j hj) s m clean]
    exact foldBlockModel_value 0 _ _ false (lift24_cells_geometry subtract j hj) s.basis

theorem lift24_forward_carry (subtract : Bool) (j : Nat) (hj : j<2) (s : State) (m : List Bool)
    (ready : Lift24Ready j s.basis) :
    (run (lift24Forward subtract j) m s).basis (59+j)=lift24Carry subtract j s.basis := by
  rw [lift24Forward,if_pos hj]
  simpa only [lift24Saved,if_pos rfl] using
    foldBlockSave_carries 0 (lift24Top j) (lift24Saved subtract j) _ _
      (lift24_cells_geometry subtract j (by omega)) (lift24_saved_mem subtract j hj)
      (lift24_cells_top subtract j (by omega)) (lift24_top_distinct j hj) s m
      (lift24_forward_clean subtract j (by omega) s.basis ready)
      (lift24Saved subtract j) (lift24_saved_mem subtract j hj)

private theorem word_split (subtract : Bool) (j : Nat) (hj : j<3) :
    lift24Word=List.range' 1 (lift24Starts[j]?.getD 0)++
      (lift24Cells subtract j false).map FoldCell.data++
      List.range' (1+lift24Starts[j]?.getD 0+lift24Sizes[j]?.getD 0)
        (58-(lift24Starts[j]?.getD 0+lift24Sizes[j]?.getD 0)) := by
  cases subtract <;> interval_cases j <;> decide

private theorem outside_frame (subtract : Bool) (j : Nat) (hj : j<3) (s : State) (m : List Bool)
    (ready : Lift24Ready j s.basis) (q : Wire) (hq : q<59)
    (outside : q<1+lift24Starts[j]?.getD 0 ∨
      1+lift24Starts[j]?.getD 0+lift24Sizes[j]?.getD 0≤q) :
    (run (lift24Forward subtract j) m s).basis q=s.basis q := by
  apply lift24_forward_frame subtract j hj s m ready
  intro mem
  have bounds := lift24_cells_bounds subtract j false q mem
  simp only [Bool.false_eq_true,if_false] at bounds
  dsimp only [Wire] at *
  omega

/-- Exact whole-word conservation for one physical block, including its
carry. The final block's discarded carry remains a mathematical Boolean. -/
theorem lift24_forward_conservation (subtract : Bool) (j : Nat) (hj : j<3) (s : State) (m : List Bool)
    (ready : Lift24Ready j s.basis) :
    regValue lift24Word (run (lift24Forward subtract j) m s).basis+
      2^(lift24Starts[j]?.getD 0+lift24Sizes[j]?.getD 0)*(lift24Carry subtract j s.basis).toNat=
    regValue lift24Word s.basis+2^(lift24Starts[j]?.getD 0)*
      (foldBlockLiteral (lift24Cells subtract j false) (s.basis 0)+
        (((lift24Input j).map s.basis).getD false).toNat) := by
  have lowSame : regValue (List.range' 1 (lift24Starts[j]?.getD 0))
      (run (lift24Forward subtract j) m s).basis=
      regValue (List.range' 1 (lift24Starts[j]?.getD 0)) s.basis := by
    apply regValue_congr
    intro q hq
    have part := lift24_partition j hj
    simp only [List.mem_range'] at hq
    apply outside_frame subtract j hj s m ready q (by dsimp only [Wire]; omega) (Or.inl (by dsimp only [Wire]; omega))
  have highSame : regValue (List.range' (1+lift24Starts[j]?.getD 0+lift24Sizes[j]?.getD 0)
      (58-(lift24Starts[j]?.getD 0+lift24Sizes[j]?.getD 0)))
      (run (lift24Forward subtract j) m s).basis=
      regValue (List.range' (1+lift24Starts[j]?.getD 0+lift24Sizes[j]?.getD 0)
        (58-(lift24Starts[j]?.getD 0+lift24Sizes[j]?.getD 0))) s.basis := by
    apply regValue_congr
    intro q hq
    have part := lift24_partition j hj
    simp only [List.mem_range'] at hq
    apply outside_frame subtract j hj s m ready q (by dsimp only [Wire]; omega) (Or.inr (by omega))
  have value := lift24_forward_value subtract j hj s m ready
  have conservation := foldBlockOverflow_value (lift24Cells subtract j false) (s.basis 0)
    (((lift24Input j).map s.basis).getD false) s.basis
  rw [←value] at conservation
  change _+_*(lift24Carry subtract j s.basis).toNat=_ at conservation
  have len : (lift24Cells subtract j false).length=lift24Sizes[j]?.getD 0 := by
    simp [lift24Cells]
  rw [word_split subtract j hj]
  simp only [regValue_append,lowSame,highSame,List.length_append,List.length_range',List.length_map,len,Nat.pow_add]
  rw [len] at conservation
  have weighted := congrArg (fun x => 2^(lift24Starts[j]?.getD 0)*x) conservation
  nlinarith only [weighted]

end ECDSAAdd.Arithmetic.Paper935
