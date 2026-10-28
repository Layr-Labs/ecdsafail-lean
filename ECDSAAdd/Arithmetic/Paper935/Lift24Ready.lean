import ECDSAAdd.Arithmetic.Paper935.Lift24Program

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def Lift24Ready (j : Nat) (s : BasisState) : Prop := ∀ i<24,j ≤ i → s (59+i)=false

def lift24Saved (subtract : Bool) (j : Nat) : FoldCell :=
  ⟨(lift24Literal subtract).testBit (lift24Starts[j]?.getD 0),1+lift24Starts[j]?.getD 0,59+j⟩

theorem lift24_saved_mem (subtract : Bool) (j : Nat) (hj : j<2) :
    lift24Saved subtract j∈lift24Cells subtract j false := by
  cases subtract <;> interval_cases j <;> decide

theorem lift24_cells_bounds (subtract : Bool) (j : Nat) (erase : Bool) (q : Wire)
    (hq : q∈(lift24Cells subtract j erase).flatMap FoldCell.wires) :
    (1+lift24Starts[j]?.getD 0≤q ∧ q<1+lift24Starts[j]?.getD 0+lift24Sizes[j]?.getD 0) ∨
    (59+j+(if erase then 1 else 0)≤q ∧ q<59+j+(if erase then 1 else 0)+lift24Sizes[j]?.getD 0) := by
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  simp only [FoldCell.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
  change q=1+lift24Starts[j]?.getD 0+i ∨ q=59+j+(if erase then 1 else 0)+i at hq
  dsimp only [Wire] at *
  rcases hq with hq | hq <;> omega

theorem lift24_forward_clean (subtract : Bool) (j : Nat) (hj : j<3) (s : BasisState)
    (ready : Lift24Ready j s) : ∀ b∈lift24Cells subtract j false,s b.carry=false := by
  intro b hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have cap := (lift24_forward_capacity j hj).2
  change s (59+j+0+i)=false
  rw [show 59+j+0+i=59+(j+i) by omega]
  exact ready (j+i) (by omega) (by omega)

theorem lift24_comparator_clean (subtract : Bool) (j : Nat) (hj : j<2) (s : BasisState)
    (ready : Lift24Ready (j+1) s) : ∀ b∈lift24Cells subtract j true,s b.carry=false := by
  intro b hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have cap := lift24_erase_capacity j hj
  change s (59+j+1+i)=false
  rw [show 59+j+1+i=59+(j+1+i) by omega]
  exact ready (j+1+i) (by omega) (by omega)

theorem lift24_forward_ready (subtract : Bool) (j : Nat) (hj : j<2) (s : State) (m : List Bool)
    (ready : Lift24Ready j s.basis) : Lift24Ready (j+1) (run (lift24Forward subtract j) m s).basis := by
  intro i hi hij
  have clean := lift24_forward_clean subtract j (by omega) s.basis ready
  have geometry := lift24_cells_geometry subtract j (by omega)
  have saved := lift24_saved_mem subtract j hj
  have top := lift24_cells_top subtract j (by omega)
  have different := lift24_top_distinct j hj
  rw [lift24Forward,if_pos hj]
  by_cases inside : i<j+lift24Sizes[j]?.getD 0
  · let cell : FoldCell := ⟨(lift24Literal subtract).testBit (lift24Starts[j]?.getD 0+(i-j)),
      1+lift24Starts[j]?.getD 0+(i-j),59+j+0+(i-j)⟩
    have member : cell∈lift24Cells subtract j false :=
      List.mem_map.mpr ⟨i-j,List.mem_range.mpr (by omega),rfl⟩
    have h := foldBlockSave_carries 0 (lift24Top j) (lift24Saved subtract j) _ _
      geometry saved top different s m clean cell member
    have carry : cell.carry=59+i := by dsimp only [cell,Wire]; omega
    simpa only [carry,lift24Saved,show ¬59+i=59+j by omega,if_false] using h
  · change (run (foldBlockSave 0 (lift24Top j) (lift24Saved subtract j).carry (lift24Cells subtract j false) (lift24Input j)) m s).basis (59+i)=false
    rw [foldBlockSave_frame 0 (lift24Top j) (lift24Saved subtract j) _ _ geometry saved top different s m clean]
    · exact ready i hi (by omega)
    · intro mem
      have bounds := lift24_cells_bounds subtract j false (59+i) mem
      have part := (lift24_partition j (by omega)).2
      simp only [Bool.false_eq_true,if_false] at bounds
      dsimp only [Wire] at bounds
      omega

theorem lift24_last_ready (subtract : Bool) (s : State) (m : List Bool)
    (ready : Lift24Ready 2 s.basis) : Lift24Ready 2 (run (lift24Forward subtract 2) m s).basis := by
  intro i hi lower
  have clean := lift24_forward_clean subtract 2 (by decide) s.basis ready
  rw [lift24Forward,if_neg (by decide),foldBlock_run 0 _ _ true false
    (lift24_cells_geometry subtract 2 (by decide)) s m clean]
  let cell : FoldCell := ⟨(lift24Literal subtract).testBit (36+(i-2)),1+36+(i-2),59+2+0+(i-2)⟩
  have member : cell∈lift24Cells subtract 2 false :=
    List.mem_map.mpr ⟨i-2,List.mem_range.mpr (by change i-2<22; omega),rfl⟩
  have carry : cell.carry=59+i := by dsimp only [cell,Wire]; omega
  simpa only [carry] using foldBlockModel_carry_clean 0 _ _ true false
    (lift24_cells_geometry subtract 2 (by decide)) s.basis cell member (Or.inl rfl)

theorem lift24_forward_frame (subtract : Bool) (j : Nat) (hj : j<3) (s : State) (m : List Bool)
    (ready : Lift24Ready j s.basis) (q : Wire)
    (hq : q∉(lift24Cells subtract j false).flatMap FoldCell.wires) :
    (run (lift24Forward subtract j) m s).basis q=s.basis q := by
  have clean := lift24_forward_clean subtract j hj s.basis ready
  by_cases h : j<2
  · rw [lift24Forward,if_pos h]
    exact foldBlockSave_frame 0 (lift24Top j) (lift24Saved subtract j) _ _
      (lift24_cells_geometry subtract j hj) (lift24_saved_mem subtract j h)
      (lift24_cells_top subtract j hj) (lift24_top_distinct j h) s m clean q hq
  · rw [lift24Forward,if_neg h,foldBlock_run 0 _ _ true false (lift24_cells_geometry subtract j hj) s m clean]
    exact foldBlockModel_frame 0 _ _ true false s.basis q hq

theorem lift24_forward_phase (subtract : Bool) (j : Nat) (hj : j<3) (s : State) (m : List Bool)
    (ready : Lift24Ready j s.basis) : (run (lift24Forward subtract j) m s).phase=s.phase := by
  have clean := lift24_forward_clean subtract j hj s.basis ready
  by_cases h : j<2
  · rw [lift24Forward,if_pos h]
    have result := foldBlockSave_run 0 (lift24Top j) (lift24Saved subtract j) _ _
      (lift24_cells_geometry subtract j hj) (lift24_saved_mem subtract j h)
      (lift24_cells_top subtract j hj) (lift24_top_distinct j h) s m clean
    have phase := congrArg State.phase result
    exact phase
  · rw [lift24Forward,if_neg h,foldBlock_run 0 _ _ true false (lift24_cells_geometry subtract j hj) s m clean]

end ECDSAAdd.Arithmetic.Paper935
