import ECDSAAdd.Arithmetic.Paper935.Fold32Program

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def Fold32Ready (j : Nat) (s : BasisState) : Prop := ∀ i<32,j ≤ i → s (258+i)=false

def fold32Saved (bits : Nat → Bool) (j : Nat) : FoldCell :=
  ⟨(if fold32Starts[j]?.getD 0=0 then true else bits (fold32Starts[j]?.getD 0)),1+fold32Starts[j]?.getD 0,258+j⟩

theorem fold32_saved_mem (bits : Nat → Bool) (j : Nat) (hj : j<9) :
    fold32Saved bits j∈fold32Cells bits j false := by
  apply List.mem_map.mpr
  refine ⟨0,List.mem_range.mpr ?_,?_⟩
  · have := (fold32_forward_capacity j (by omega)).1; omega
  · simp [fold32Saved]

theorem fold32_cells_bounds (bits : Nat → Bool) (j : Nat) (erase : Bool) (q : Wire)
    (hq : q∈(fold32Cells bits j erase).flatMap FoldCell.wires) :
    (1+fold32Starts[j]?.getD 0≤q ∧ q<1+fold32Starts[j]?.getD 0+fold32Sizes[j]?.getD 0) ∨
    (258+j+(if erase then 1 else 0)≤q ∧ q<258+j+(if erase then 1 else 0)+fold32Sizes[j]?.getD 0) := by
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  simp only [FoldCell.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
  change q=1+fold32Starts[j]?.getD 0+i ∨ q=258+j+(if erase then 1 else 0)+i at hq
  dsimp only [Wire] at *
  rcases hq with hq | hq <;> omega

theorem fold32_forward_clean (bits : Nat → Bool) (j : Nat) (hj : j<10) (s : BasisState)
    (ready : Fold32Ready j s) : ∀ b∈fold32Cells bits j false,s b.carry=false := by
  intro b hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have cap := (fold32_forward_capacity j hj).2
  change s (258+j+0+i)=false
  rw [show 258+j+0+i=258+(j+i) by omega]
  exact ready (j+i) (by omega) (by omega)

theorem fold32_comparator_clean (bits : Nat → Bool) (j : Nat) (hj : j<9) (s : BasisState)
    (ready : Fold32Ready (j+1) s) : ∀ b∈fold32Cells bits j true,s b.carry=false := by
  intro b hb
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  have cap := fold32_erase_capacity j hj
  change s (258+j+1+i)=false
  rw [show 258+j+1+i=258+(j+1+i) by omega]
  exact ready (j+1+i) (by omega) (by omega)

theorem fold32_forward_ready (bits : Nat → Bool) (j : Nat) (hj : j<9) (s : State) (m : List Bool)
    (ready : Fold32Ready j s.basis) : Fold32Ready (j+1) (run (fold32Forward bits j) m s).basis := by
  intro i hi hij
  have clean := fold32_forward_clean bits j (by omega) s.basis ready
  have geometry := fold32_cells_geometry bits j (by omega)
  have saved := fold32_saved_mem bits j hj
  have top := fold32_cells_top bits j (by omega)
  have different := fold32_top_distinct j hj
  rw [fold32Forward,if_pos hj]
  by_cases inside : i<j+fold32Sizes[j]?.getD 0
  · let cell : FoldCell := ⟨(if fold32Starts[j]?.getD 0+(i-j)=0 then true else bits (fold32Starts[j]?.getD 0+(i-j))),
      1+fold32Starts[j]?.getD 0+(i-j),258+j+0+(i-j)⟩
    have member : cell∈fold32Cells bits j false :=
      List.mem_map.mpr ⟨i-j,List.mem_range.mpr (by omega),rfl⟩
    have h := foldBlockSave_carries 0 (fold32Top j) (fold32Saved bits j) _ _
      geometry saved top different s m clean cell member
    have carry : cell.carry=258+i := by dsimp only [cell,Wire]; omega
    simpa only [carry,fold32Saved,show ¬258+i=258+j by omega,if_false] using h
  · change (run (foldBlockSave 0 (fold32Top j) (fold32Saved bits j).carry (fold32Cells bits j false) (fold32Input j)) m s).basis (258+i)=false
    rw [foldBlockSave_frame 0 (fold32Top j) (fold32Saved bits j) _ _ geometry saved top different s m clean]
    · exact ready i hi (by omega)
    · intro mem
      have bounds := fold32_cells_bounds bits j false (258+i) mem
      have part := (fold32_partition j (by omega)).2
      simp only [Bool.false_eq_true,if_false] at bounds
      dsimp only [Wire] at bounds
      omega

theorem fold32_last_ready (bits : Nat → Bool) (s : State) (m : List Bool)
    (ready : Fold32Ready 9 s.basis) : Fold32Ready 9 (run (fold32Forward bits 9) m s).basis := by
  intro i hi lower
  have clean := fold32_forward_clean bits 9 (by decide) s.basis ready
  rw [fold32Forward,if_neg (by decide),foldBlock_run 0 _ _ true false
    (fold32_cells_geometry bits 9 (by decide)) s m clean]
  let cell : FoldCell := ⟨(if 234+(i-9)=0 then true else bits (234+(i-9))),1+234+(i-9),258+9+0+(i-9)⟩
  have member : cell∈fold32Cells bits 9 false :=
    List.mem_map.mpr ⟨i-9,List.mem_range.mpr (by change i-9<23; omega),rfl⟩
  have carry : cell.carry=258+i := by dsimp only [cell,Wire]; omega
  simpa only [carry] using foldBlockModel_carry_clean 0 _ _ true false
    (fold32_cells_geometry bits 9 (by decide)) s.basis cell member (Or.inl rfl)

theorem fold32_forward_frame (bits : Nat → Bool) (j : Nat) (hj : j<10) (s : State) (m : List Bool)
    (ready : Fold32Ready j s.basis) (q : Wire)
    (hq : q∉(fold32Cells bits j false).flatMap FoldCell.wires) :
    (run (fold32Forward bits j) m s).basis q=s.basis q := by
  have clean := fold32_forward_clean bits j hj s.basis ready
  by_cases h : j<9
  · rw [fold32Forward,if_pos h]
    exact foldBlockSave_frame 0 (fold32Top j) (fold32Saved bits j) _ _
      (fold32_cells_geometry bits j hj) (fold32_saved_mem bits j h)
      (fold32_cells_top bits j hj) (fold32_top_distinct j h) s m clean q hq
  · rw [fold32Forward,if_neg h,foldBlock_run 0 _ _ true false (fold32_cells_geometry bits j hj) s m clean]
    exact foldBlockModel_frame 0 _ _ true false s.basis q hq

theorem fold32_forward_phase (bits : Nat → Bool) (j : Nat) (hj : j<10) (s : State) (m : List Bool)
    (ready : Fold32Ready j s.basis) : (run (fold32Forward bits j) m s).phase=s.phase := by
  have clean := fold32_forward_clean bits j hj s.basis ready
  by_cases h : j<9
  · rw [fold32Forward,if_pos h]
    have result := foldBlockSave_run 0 (fold32Top j) (fold32Saved bits j) _ _
      (fold32_cells_geometry bits j hj) (fold32_saved_mem bits j h)
      (fold32_cells_top bits j hj) (fold32_top_distinct j h) s m clean
    have phase := congrArg State.phase result
    exact phase
  · rw [fold32Forward,if_neg h,foldBlock_run 0 _ _ true false (fold32_cells_geometry bits j hj) s m clean]

end ECDSAAdd.Arithmetic.Paper935
