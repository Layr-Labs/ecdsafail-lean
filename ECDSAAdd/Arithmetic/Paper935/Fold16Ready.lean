import ECDSAAdd.Arithmetic.Paper935.Fold16Program

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def Fold16Ready (j : Nat) (s : BasisState) : Prop := ∀ i<16,j ≤ i → s (59+i)=false

def fold16Saved (subtract : Bool) (j : Nat) : FoldCell :=
  ⟨(fold16Literal subtract).testBit (fold16Starts[j]?.getD 0),1+fold16Starts[j]?.getD 0,59+j⟩

theorem fold16_saved_mem (subtract : Bool) (j : Nat) (hj : j<4) :
    fold16Saved subtract j∈fold16Cells subtract j false := by
  cases subtract <;> interval_cases j <;> decide

theorem fold16_cells_bounds (subtract : Bool) (j : Nat) (erase : Bool) (q : Wire)
    (hq : q∈(fold16Cells subtract j erase).flatMap FoldCell.wires) :
    (1+fold16Starts[j]?.getD 0≤q ∧ q<1+fold16Starts[j]?.getD 0+fold16Sizes[j]?.getD 0) ∨
    (59+j+(if erase then 1 else 0)≤q ∧ q<59+j+(if erase then 1 else 0)+fold16Sizes[j]?.getD 0) := by
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  simp only [FoldCell.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
  change q=1+fold16Starts[j]?.getD 0+i ∨ q=59+j+(if erase then 1 else 0)+i at hq
  dsimp only [Wire] at *
  rcases hq with hq | hq <;> omega

theorem fold16_forward_clean (subtract : Bool) (j : Nat) (hj : j<5) (s : BasisState)
    (ready : Fold16Ready j s) : ∀ b∈fold16Cells subtract j false,s b.carry=false := by
  intro b hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have cap := (fold16_forward_capacity j hj).2
  change s (59+j+0+i)=false
  rw [show 59+j+0+i=59+(j+i) by omega]
  exact ready (j+i) (by omega) (by omega)

theorem fold16_comparator_clean (subtract : Bool) (j : Nat) (hj : j<4) (s : BasisState)
    (ready : Fold16Ready (j+1) s) : ∀ b∈fold16Cells subtract j true,s b.carry=false := by
  intro b hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have cap := fold16_erase_capacity j hj
  change s (59+j+1+i)=false
  rw [show 59+j+1+i=59+(j+1+i) by omega]
  exact ready (j+1+i) (by omega) (by omega)

theorem fold16_forward_ready (subtract : Bool) (j : Nat) (hj : j<4) (s : State) (m : List Bool)
    (ready : Fold16Ready j s.basis) : Fold16Ready (j+1) (run (fold16Forward subtract j) m s).basis := by
  intro i hi hij
  have clean := fold16_forward_clean subtract j (by omega) s.basis ready
  have geometry := fold16_cells_geometry subtract j (by omega)
  have saved := fold16_saved_mem subtract j hj
  have top := fold16_cells_top subtract j (by omega)
  have different := fold16_top_distinct j hj
  rw [fold16Forward,if_pos hj]
  by_cases inside : i<j+fold16Sizes[j]?.getD 0
  · let cell : FoldCell := ⟨(fold16Literal subtract).testBit (fold16Starts[j]?.getD 0+(i-j)),
      1+fold16Starts[j]?.getD 0+(i-j),59+j+0+(i-j)⟩
    have member : cell∈fold16Cells subtract j false :=
      List.mem_map.mpr ⟨i-j,List.mem_range.mpr (by omega),rfl⟩
    have h := foldBlockSave_carries 0 (fold16Top j) (fold16Saved subtract j) _ _
      geometry saved top different s m clean cell member
    have carry : cell.carry=59+i := by dsimp only [cell,Wire]; omega
    simpa only [carry,fold16Saved,show ¬59+i=59+j by omega,if_false] using h
  · change (run (foldBlockSave 0 (fold16Top j) (fold16Saved subtract j).carry (fold16Cells subtract j false) (fold16Input j)) m s).basis (59+i)=false
    rw [foldBlockSave_frame 0 (fold16Top j) (fold16Saved subtract j) _ _ geometry saved top different s m clean]
    · exact ready i hi (by omega)
    · intro mem
      have bounds := fold16_cells_bounds subtract j false (59+i) mem
      have part := (fold16_partition j (by omega)).2
      simp only [Bool.false_eq_true,if_false] at bounds
      dsimp only [Wire] at bounds
      omega

theorem fold16_last_ready (subtract : Bool) (s : State) (m : List Bool)
    (ready : Fold16Ready 4 s.basis) : Fold16Ready 4 (run (fold16Forward subtract 4) m s).basis := by
  intro i hi lower
  have clean := fold16_forward_clean subtract 4 (by decide) s.basis ready
  rw [fold16Forward,if_neg (by decide),foldBlock_run 0 _ _ true false
    (fold16_cells_geometry subtract 4 (by decide)) s m clean]
  let cell : FoldCell := ⟨(fold16Literal subtract).testBit (46+(i-4)),1+46+(i-4),59+4+0+(i-4)⟩
  have member : cell∈fold16Cells subtract 4 false :=
    List.mem_map.mpr ⟨i-4,List.mem_range.mpr (by change i-4<12; omega),rfl⟩
  have carry : cell.carry=59+i := by dsimp only [cell,Wire]; omega
  simpa only [carry] using foldBlockModel_carry_clean 0 _ _ true false
    (fold16_cells_geometry subtract 4 (by decide)) s.basis cell member (Or.inl rfl)

theorem fold16_forward_frame (subtract : Bool) (j : Nat) (hj : j<5) (s : State) (m : List Bool)
    (ready : Fold16Ready j s.basis) (q : Wire)
    (hq : q∉(fold16Cells subtract j false).flatMap FoldCell.wires) :
    (run (fold16Forward subtract j) m s).basis q=s.basis q := by
  have clean := fold16_forward_clean subtract j hj s.basis ready
  by_cases h : j<4
  · rw [fold16Forward,if_pos h]
    exact foldBlockSave_frame 0 (fold16Top j) (fold16Saved subtract j) _ _
      (fold16_cells_geometry subtract j hj) (fold16_saved_mem subtract j h)
      (fold16_cells_top subtract j hj) (fold16_top_distinct j h) s m clean q hq
  · rw [fold16Forward,if_neg h,foldBlock_run 0 _ _ true false (fold16_cells_geometry subtract j hj) s m clean]
    exact foldBlockModel_frame 0 _ _ true false s.basis q hq

theorem fold16_forward_phase (subtract : Bool) (j : Nat) (hj : j<5) (s : State) (m : List Bool)
    (ready : Fold16Ready j s.basis) : (run (fold16Forward subtract j) m s).phase=s.phase := by
  have clean := fold16_forward_clean subtract j hj s.basis ready
  by_cases h : j<4
  · rw [fold16Forward,if_pos h]
    have result := foldBlockSave_run 0 (fold16Top j) (fold16Saved subtract j) _ _
      (fold16_cells_geometry subtract j hj) (fold16_saved_mem subtract j h)
      (fold16_cells_top subtract j hj) (fold16_top_distinct j h) s m clean
    have phase := congrArg State.phase result
    exact phase
  · rw [fold16Forward,if_neg h,foldBlock_run 0 _ _ true false (fold16_cells_geometry subtract j hj) s m clean]

end ECDSAAdd.Arithmetic.Paper935
