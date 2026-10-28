import ECDSAAdd.Arithmetic.Paper935.Fold32Ready

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def Fold32Keeper (bits : Nat → Bool) (j : Nat) (s : BasisState) : Prop :=
  s (258+j)=(s 0 && decide (regValue ((fold32Cells bits j false).map FoldCell.data) s<
    foldBlockLiteral (fold32Cells bits j false) true+(((fold32Input j).map s).getD false).toNat))

/-- Clean unoccupied pool plus exact predicates for every occupied keeper. -/
def Fold32Invariant (bits : Nat → Bool) (j : Nat) (s : BasisState) : Prop :=
  Fold32Ready j s ∧ ∀ i<j,Fold32Keeper bits i s

theorem fold32_forward_prefix (bits : Nat → Bool) (j : Nat) (hj : j<10) (s : State) (m : List Bool)
    (ready : Fold32Ready j s.basis) (q : Wire)
    (before : q<1+fold32Starts[j]?.getD 0 ∨ (258≤q ∧ q<258+j)) :
    (run (fold32Forward bits j) m s).basis q=s.basis q := by
  apply fold32_forward_frame bits j hj s m ready q
  intro mem
  have bounds := fold32_cells_bounds bits j false q mem
  have part := (fold32_partition j hj).2
  simp only [Bool.false_eq_true,if_false] at bounds
  dsimp only [Wire] at *
  omega

private theorem data_bound (bits : Nat → Bool) (j : Nat) (q : Wire)
    (hq : q∈(fold32Cells bits j false).map FoldCell.data) :
    1+fold32Starts[j]?.getD 0≤q ∧ q<1+fold32Starts[j]?.getD 0+fold32Sizes[j]?.getD 0 := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  dsimp only [Wire]
  omega

private theorem blocks_order (i j : Nat) (hij : i<j) (hj : j<10) :
    fold32Starts[i]?.getD 0+fold32Sizes[i]?.getD 0≤fold32Starts[j]?.getD 0 := by
  have hi : i<10 := by omega
  interval_cases i <;> interval_cases j <;> simp_all [fold32Starts,fold32Sizes]

private theorem keeper_congr (bits : Nat → Bool) (i : Nat) (s t : BasisState)
    (hc : s 0=t 0) (hk : s (258+i)=t (258+i))
    (hin : ((fold32Input i).map s).getD false=((fold32Input i).map t).getD false)
    (hd : regValue ((fold32Cells bits i false).map FoldCell.data) s=
      regValue ((fold32Cells bits i false).map FoldCell.data) t) :
    Fold32Keeper bits i s ↔ Fold32Keeper bits i t := by
  simp only [Fold32Keeper,hc,hk,hin,hd]

theorem fold32_forward_preserves_keeper (bits : Nat → Bool) (i j : Nat) (hij : i<j) (hj : j<10)
    (s : State) (m : List Bool) (ready : Fold32Ready j s.basis)
    (known : Fold32Keeper bits i s.basis) :
    Fold32Keeper bits i (run (fold32Forward bits j) m s).basis := by
  apply (keeper_congr bits i _ s.basis ?_ ?_ ?_ ?_).mpr known
  · exact fold32_forward_prefix bits j hj s m ready 0 (Or.inl (by dsimp only [Wire]; omega))
  · apply fold32_forward_prefix bits j hj s m ready (258+i)
    right
    dsimp only [Wire]
    omega
  · by_cases hi : i=0
    · simp [fold32Input,hi]
    · simp only [fold32Input,if_neg hi,Option.map_some,Option.getD_some]
      apply fold32_forward_prefix bits j hj s m ready (258+i-1)
      right
      dsimp only [Wire]
      omega
  · apply regValue_congr
    intro q hq
    have bound := data_bound bits i q hq
    have order := blocks_order i j hij hj
    apply fold32_forward_prefix bits j hj s m ready q
    left
    dsimp only [Wire] at *
    omega

theorem fold32_input_inactive (bits : Nat → Bool) (j : Nat) (s : BasisState)
    (keepers : ∀ i<j,Fold32Keeper bits i s) (off : s 0=false) :
    ((fold32Input j).map s).getD false=false := by
  by_cases hj : j=0
  · simp [fold32Input,hj]
  · have known := keepers (j-1) (by omega)
    have val : s (258+(j-1))=false := by simpa only [Fold32Keeper,off,Bool.false_and] using known
    simp only [fold32Input,if_neg hj,Option.map_some,Option.getD_some]
    rw [show (258+j-1 : Wire)=258+(j-1) by dsimp only [Wire]; omega]
    exact val

theorem fold32_forward_invariant (bits : Nat → Bool) (j : Nat) (hj : j<9) (s : State) (m : List Bool)
    (inv : Fold32Invariant bits j s.basis) :
    Fold32Invariant bits (j+1) (run (fold32Forward bits j) m s).basis := by
  refine ⟨fold32_forward_ready bits j hj s m inv.1,?_⟩
  intro i hi
  by_cases old : i<j
  · exact fold32_forward_preserves_keeper bits i j old (by omega) s m inv.1 (inv.2 i old)
  · have eq : i=j := by omega
    subst i
    have clean := fold32_forward_clean bits j (by omega) s.basis inv.1
    have known := foldBlockSave_keeper 0 (fold32Top j) (fold32Saved bits j) _ _
      (fold32_cells_geometry bits j (by omega)) (fold32_saved_mem bits j hj)
      (fold32_cells_top bits j (by omega)) (fold32_top_distinct j hj) s m clean
      (fold32_input_inactive bits j s.basis inv.2)
    have ctrl := fold32_forward_prefix bits j (by omega) s m inv.1 0 (Or.inl (by dsimp only [Wire]; omega))
    have input : ((fold32Input j).map (run (fold32Forward bits j) m s).basis).getD false=
        ((fold32Input j).map s.basis).getD false := by
      by_cases hz : j=0
      · simp [fold32Input,hz]
      · simp only [fold32Input,if_neg hz,Option.map_some,Option.getD_some]
        apply fold32_forward_prefix bits j (by omega) s m inv.1 (258+j-1)
        right
        dsimp only [Wire]
        omega
    unfold Fold32Keeper
    rw [ctrl,input]
    simpa only [fold32Forward,if_pos hj,fold32Saved] using known

theorem fold32_last_invariant (bits : Nat → Bool) (s : State) (m : List Bool)
    (inv : Fold32Invariant bits 9 s.basis) :
    Fold32Invariant bits 9 (run (fold32Forward bits 9) m s).basis := by
  refine ⟨fold32_last_ready bits s m inv.1,?_⟩
  intro i hi
  exact fold32_forward_preserves_keeper bits i 9 hi (by decide) s m inv.1 (inv.2 i hi)

private theorem erase_views (bits : Nat → Bool) (j : Nat) (_hj : j<9) :
    (fold32Cells bits j true).map FoldCell.data=(fold32Cells bits j false).map FoldCell.data ∧
    foldBlockLiteral (fold32Cells bits j true) true=foldBlockLiteral (fold32Cells bits j false) true := by
  constructor
  · simp [fold32Cells,List.map_map]
  · unfold fold32Cells
    generalize List.range (fold32Sizes[j]?.getD 0) = indices
    induction indices with
    | nil => rfl
    | cons i rest ih => simpa only [List.map_cons,foldBlockLiteral] using congrArg (fun n => ((if fold32Starts[j]?.getD 0+i=0 then true else bits (fold32Starts[j]?.getD 0+i)) && true).toNat+2*n) ih

theorem fold32_erase_run (bits : Nat → Bool) (j : Nat) (hj : j<9) (s : State) (m : List Bool)
    (inv : Fold32Invariant bits (j+1) s.basis) :
    run (fold32Erase bits j) m s=⟨s.phase,writeBit s.basis (258+j) false⟩ := by
  apply foldKeeperErase_clean 0 (258+j) (fold32Cells bits j true) (fold32Input j)
    (fold32_erase_geometry bits j hj) s m (fold32_comparator_clean bits j hj s.basis inv.1)
  rw [(erase_views bits j hj).1,(erase_views bits j hj).2]
  exact inv.2 j (by omega)

theorem fold32_erase_invariant (bits : Nat → Bool) (j : Nat) (hj : j<9) (s : State) (m : List Bool)
    (inv : Fold32Invariant bits (j+1) s.basis) :
    Fold32Invariant bits j (run (fold32Erase bits j) m s).basis := by
  rw [fold32_erase_run bits j hj s m inv]
  constructor
  · intro i hi hij
    by_cases eq : i=j
    · subst i; simp [writeBit]
    · have away : (258+i : Wire)≠258+j := by dsimp only [Wire]; omega
      simpa only [writeBit,Function.update_of_ne away] using inv.1 i hi (by omega)
  · intro i hij
    apply (keeper_congr bits i _ s.basis ?_ ?_ ?_ ?_).mpr (inv.2 i (by omega))
    · have away : (0 : Wire)≠258+j := by dsimp only [Wire]; omega
      simp only [writeBit,Function.update_of_ne away]
    · have away : (258+i : Wire)≠258+j := by dsimp only [Wire]; omega
      simp only [writeBit,Function.update_of_ne away]
    · by_cases hz : i=0
      · simp [fold32Input,hz]
      · have away : (258+i-1 : Wire)≠258+j := by dsimp only [Wire]; omega
        simp only [fold32Input,if_neg hz,Option.map_some,Option.getD_some,writeBit,Function.update_of_ne away]
    · apply regValue_congr
      intro q hq
      have bound := data_bound bits i q hq
      have part := (fold32_partition i (by omega)).2
      have away : q≠258+j := by dsimp only [Wire] at *; omega
      simp only [writeBit,Function.update_of_ne away]

end ECDSAAdd.Arithmetic.Paper935
