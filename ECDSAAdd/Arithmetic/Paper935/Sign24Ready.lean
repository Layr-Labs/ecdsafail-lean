import ECDSAAdd.Arithmetic.Paper935.Sign24Program

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def Sign24Ready (j : Nat) (s : BasisState) : Prop := ∀ i<24,j ≤ i → s (59+i)=false

def sign24Saved (subtract : Bool) (j : Nat) : FoldCell :=
  ⟨(sign24Literal subtract).testBit (sign24Starts[j]?.getD 0),1+sign24Starts[j]?.getD 0,59+j⟩

theorem sign24_saved_mem (subtract : Bool) (j : Nat) (hj : j<2) :
    sign24Saved subtract j∈sign24Cells subtract j false := by
  cases subtract <;> interval_cases j <;> decide

theorem sign24_cells_bounds (subtract : Bool) (j : Nat) (erase : Bool) (q : Wire)
    (hq : q∈(sign24Cells subtract j erase).flatMap FoldCell.wires) :
    (1+sign24Starts[j]?.getD 0≤q ∧ q<1+sign24Starts[j]?.getD 0+sign24Sizes[j]?.getD 0) ∨
    (59+j+(if erase then 1 else 0)≤q ∧ q<59+j+(if erase then 1 else 0)+sign24Sizes[j]?.getD 0) := by
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  simp only [FoldCell.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
  change q=1+sign24Starts[j]?.getD 0+i ∨ q=59+j+(if erase then 1 else 0)+i at hq
  dsimp only [Wire] at *
  rcases hq with hq | hq <;> omega

theorem sign24_forward_clean (subtract : Bool) (j : Nat) (hj : j<3) (s : BasisState)
    (ready : Sign24Ready j s) : ∀ b∈sign24Cells subtract j false,s b.carry=false := by
  intro b hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have cap := (sign24_forward_capacity j hj).2
  change s (59+j+0+i)=false
  rw [show 59+j+0+i=59+(j+i) by omega]
  exact ready (j+i) (by omega) (by omega)

theorem sign24_comparator_clean (subtract : Bool) (j : Nat) (hj : j<2) (s : BasisState)
    (ready : Sign24Ready (j+1) s) : ∀ b∈sign24Cells subtract j true,s b.carry=false := by
  intro b hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have cap := sign24_erase_capacity j hj
  change s (59+j+1+i)=false
  rw [show 59+j+1+i=59+(j+1+i) by omega]
  exact ready (j+1+i) (by omega) (by omega)

theorem sign24_forward_ready (subtract : Bool) (j : Nat) (hj : j<2) (s : State) (m : List Bool)
    (ready : Sign24Ready j s.basis) : Sign24Ready (j+1) (run (sign24Forward subtract j) m s).basis := by
  intro i hi hij
  have clean := sign24_forward_clean subtract j (by omega) s.basis ready
  have geometry := sign24_cells_geometry subtract j (by omega)
  have saved := sign24_saved_mem subtract j hj
  have top := sign24_cells_top subtract j (by omega)
  have different := sign24_top_distinct j hj
  rw [sign24Forward,if_pos hj]
  by_cases inside : i<j+sign24Sizes[j]?.getD 0
  · let cell : FoldCell := ⟨(sign24Literal subtract).testBit (sign24Starts[j]?.getD 0+(i-j)),
      1+sign24Starts[j]?.getD 0+(i-j),59+j+0+(i-j)⟩
    have member : cell∈sign24Cells subtract j false :=
      List.mem_map.mpr ⟨i-j,List.mem_range.mpr (by omega),rfl⟩
    have h := foldBlockSave_carries 0 (sign24Top j) (sign24Saved subtract j) _ _
      geometry saved top different s m clean cell member
    have carry : cell.carry=59+i := by dsimp only [cell,Wire]; omega
    simpa only [carry,sign24Saved,show ¬59+i=59+j by omega,if_false] using h
  · change (run (foldBlockSave 0 (sign24Top j) (sign24Saved subtract j).carry (sign24Cells subtract j false) (sign24Input j)) m s).basis (59+i)=false
    rw [foldBlockSave_frame 0 (sign24Top j) (sign24Saved subtract j) _ _ geometry saved top different s m clean]
    · exact ready i hi (by omega)
    · intro mem
      have bounds := sign24_cells_bounds subtract j false (59+i) mem
      have part := (sign24_partition j (by omega)).2
      simp only [Bool.false_eq_true,if_false] at bounds
      dsimp only [Wire] at bounds
      omega

theorem sign24_last_ready (subtract : Bool) (s : State) (m : List Bool)
    (ready : Sign24Ready 2 s.basis) : Sign24Ready 2 (run (sign24Forward subtract 2) m s).basis := by
  intro i hi lower
  have clean := sign24_forward_clean subtract 2 (by decide) s.basis ready
  rw [sign24Forward,if_neg (by decide),foldBlock_run 0 _ _ true false
    (sign24_cells_geometry subtract 2 (by decide)) s m clean]
  let cell : FoldCell := ⟨(sign24Literal subtract).testBit (36+(i-2)),1+36+(i-2),59+2+0+(i-2)⟩
  have member : cell∈sign24Cells subtract 2 false :=
    List.mem_map.mpr ⟨i-2,List.mem_range.mpr (by change i-2<22; omega),rfl⟩
  have carry : cell.carry=59+i := by dsimp only [cell,Wire]; omega
  simpa only [carry] using foldBlockModel_carry_clean 0 _ _ true false
    (sign24_cells_geometry subtract 2 (by decide)) s.basis cell member (Or.inl rfl)

theorem sign24_forward_frame (subtract : Bool) (j : Nat) (hj : j<3) (s : State) (m : List Bool)
    (ready : Sign24Ready j s.basis) (q : Wire)
    (hq : q∉(sign24Cells subtract j false).flatMap FoldCell.wires) :
    (run (sign24Forward subtract j) m s).basis q=s.basis q := by
  have clean := sign24_forward_clean subtract j hj s.basis ready
  by_cases h : j<2
  · rw [sign24Forward,if_pos h]
    exact foldBlockSave_frame 0 (sign24Top j) (sign24Saved subtract j) _ _
      (sign24_cells_geometry subtract j hj) (sign24_saved_mem subtract j h)
      (sign24_cells_top subtract j hj) (sign24_top_distinct j h) s m clean q hq
  · rw [sign24Forward,if_neg h,foldBlock_run 0 _ _ true false (sign24_cells_geometry subtract j hj) s m clean]
    exact foldBlockModel_frame 0 _ _ true false s.basis q hq

theorem sign24_forward_phase (subtract : Bool) (j : Nat) (hj : j<3) (s : State) (m : List Bool)
    (ready : Sign24Ready j s.basis) : (run (sign24Forward subtract j) m s).phase=s.phase := by
  have clean := sign24_forward_clean subtract j hj s.basis ready
  by_cases h : j<2
  · rw [sign24Forward,if_pos h]
    have result := foldBlockSave_run 0 (sign24Top j) (sign24Saved subtract j) _ _
      (sign24_cells_geometry subtract j hj) (sign24_saved_mem subtract j h)
      (sign24_cells_top subtract j hj) (sign24_top_distinct j h) s m clean
    have phase := congrArg State.phase result
    exact phase
  · rw [sign24Forward,if_neg h,foldBlock_run 0 _ _ true false (sign24_cells_geometry subtract j hj) s m clean]

end ECDSAAdd.Arithmetic.Paper935
