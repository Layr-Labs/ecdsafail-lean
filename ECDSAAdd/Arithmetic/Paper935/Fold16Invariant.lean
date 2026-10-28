import ECDSAAdd.Arithmetic.Paper935.Fold16Ready

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def Fold16Keeper (subtract : Bool) (j : Nat) (s : BasisState) : Prop :=
  s (59+j)=(s 0 && decide (regValue ((fold16Cells subtract j false).map FoldCell.data) s<
    foldBlockLiteral (fold16Cells subtract j false) true+(((fold16Input j).map s).getD false).toNat))

/-- Clean unoccupied pool plus exact predicates for every occupied keeper. -/
def Fold16Invariant (subtract : Bool) (j : Nat) (s : BasisState) : Prop :=
  Fold16Ready j s ∧ ∀ i<j,Fold16Keeper subtract i s

theorem fold16_forward_prefix (subtract : Bool) (j : Nat) (hj : j<5) (s : State) (m : List Bool)
    (ready : Fold16Ready j s.basis) (q : Wire)
    (before : q<1+fold16Starts[j]?.getD 0 ∨ (59≤q ∧ q<59+j)) :
    (run (fold16Forward subtract j) m s).basis q=s.basis q := by
  apply fold16_forward_frame subtract j hj s m ready q
  intro mem
  have bounds := fold16_cells_bounds subtract j false q mem
  have part := (fold16_partition j hj).2
  simp only [Bool.false_eq_true,if_false] at bounds
  dsimp only [Wire] at *
  omega

private theorem data_bound (subtract : Bool) (j : Nat) (q : Wire)
    (hq : q∈(fold16Cells subtract j false).map FoldCell.data) :
    1+fold16Starts[j]?.getD 0≤q ∧ q<1+fold16Starts[j]?.getD 0+fold16Sizes[j]?.getD 0 := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  dsimp only [Wire]
  omega

private theorem blocks_order (i j : Nat) (hij : i<j) (hj : j<5) :
    fold16Starts[i]?.getD 0+fold16Sizes[i]?.getD 0≤fold16Starts[j]?.getD 0 := by
  have hi : i<5 := by omega
  interval_cases i <;> interval_cases j <;> simp_all [fold16Starts,fold16Sizes]

private theorem keeper_congr (subtract : Bool) (i : Nat) (s t : BasisState)
    (hc : s 0=t 0) (hk : s (59+i)=t (59+i))
    (hin : ((fold16Input i).map s).getD false=((fold16Input i).map t).getD false)
    (hd : regValue ((fold16Cells subtract i false).map FoldCell.data) s=
      regValue ((fold16Cells subtract i false).map FoldCell.data) t) :
    Fold16Keeper subtract i s ↔ Fold16Keeper subtract i t := by
  simp only [Fold16Keeper,hc,hk,hin,hd]

theorem fold16_forward_preserves_keeper (subtract : Bool) (i j : Nat) (hij : i<j) (hj : j<5)
    (s : State) (m : List Bool) (ready : Fold16Ready j s.basis)
    (known : Fold16Keeper subtract i s.basis) :
    Fold16Keeper subtract i (run (fold16Forward subtract j) m s).basis := by
  apply (keeper_congr subtract i _ s.basis ?_ ?_ ?_ ?_).mpr known
  · exact fold16_forward_prefix subtract j hj s m ready 0 (Or.inl (by dsimp only [Wire]; omega))
  · apply fold16_forward_prefix subtract j hj s m ready (59+i)
    right
    dsimp only [Wire]
    omega
  · by_cases hi : i=0
    · simp [fold16Input,hi]
    · simp only [fold16Input,if_neg hi,Option.map_some,Option.getD_some]
      apply fold16_forward_prefix subtract j hj s m ready (59+i-1)
      right
      dsimp only [Wire]
      omega
  · apply regValue_congr
    intro q hq
    have bound := data_bound subtract i q hq
    have order := blocks_order i j hij hj
    apply fold16_forward_prefix subtract j hj s m ready q
    left
    dsimp only [Wire] at *
    omega

theorem fold16_input_inactive (subtract : Bool) (j : Nat) (s : BasisState)
    (keepers : ∀ i<j,Fold16Keeper subtract i s) (off : s 0=false) :
    ((fold16Input j).map s).getD false=false := by
  by_cases hj : j=0
  · simp [fold16Input,hj]
  · have known := keepers (j-1) (by omega)
    have val : s (59+(j-1))=false := by simpa only [Fold16Keeper,off,Bool.false_and] using known
    simp only [fold16Input,if_neg hj,Option.map_some,Option.getD_some]
    rw [show (59+j-1 : Wire)=59+(j-1) by dsimp only [Wire]; omega]
    exact val

theorem fold16_forward_invariant (subtract : Bool) (j : Nat) (hj : j<4) (s : State) (m : List Bool)
    (inv : Fold16Invariant subtract j s.basis) :
    Fold16Invariant subtract (j+1) (run (fold16Forward subtract j) m s).basis := by
  refine ⟨fold16_forward_ready subtract j hj s m inv.1,?_⟩
  intro i hi
  by_cases old : i<j
  · exact fold16_forward_preserves_keeper subtract i j old (by omega) s m inv.1 (inv.2 i old)
  · have eq : i=j := by omega
    subst i
    have clean := fold16_forward_clean subtract j (by omega) s.basis inv.1
    have known := foldBlockSave_keeper 0 (fold16Top j) (fold16Saved subtract j) _ _
      (fold16_cells_geometry subtract j (by omega)) (fold16_saved_mem subtract j hj)
      (fold16_cells_top subtract j (by omega)) (fold16_top_distinct j hj) s m clean
      (fold16_input_inactive subtract j s.basis inv.2)
    have ctrl := fold16_forward_prefix subtract j (by omega) s m inv.1 0 (Or.inl (by dsimp only [Wire]; omega))
    have input : ((fold16Input j).map (run (fold16Forward subtract j) m s).basis).getD false=
        ((fold16Input j).map s.basis).getD false := by
      by_cases hz : j=0
      · simp [fold16Input,hz]
      · simp only [fold16Input,if_neg hz,Option.map_some,Option.getD_some]
        apply fold16_forward_prefix subtract j (by omega) s m inv.1 (59+j-1)
        right
        dsimp only [Wire]
        omega
    unfold Fold16Keeper
    rw [ctrl,input]
    simpa only [fold16Forward,if_pos hj,fold16Saved] using known

theorem fold16_last_invariant (subtract : Bool) (s : State) (m : List Bool)
    (inv : Fold16Invariant subtract 4 s.basis) :
    Fold16Invariant subtract 4 (run (fold16Forward subtract 4) m s).basis := by
  refine ⟨fold16_last_ready subtract s m inv.1,?_⟩
  intro i hi
  exact fold16_forward_preserves_keeper subtract i 4 hi (by decide) s m inv.1 (inv.2 i hi)

private theorem erase_views (subtract : Bool) (j : Nat) (hj : j<4) :
    (fold16Cells subtract j true).map FoldCell.data=(fold16Cells subtract j false).map FoldCell.data ∧
    foldBlockLiteral (fold16Cells subtract j true) true=foldBlockLiteral (fold16Cells subtract j false) true := by
  cases subtract <;> interval_cases j <;> decide

theorem fold16_erase_run (subtract : Bool) (j : Nat) (hj : j<4) (s : State) (m : List Bool)
    (inv : Fold16Invariant subtract (j+1) s.basis) :
    run (fold16Erase subtract j) m s=⟨s.phase,writeBit s.basis (59+j) false⟩ := by
  apply foldKeeperErase_clean 0 (59+j) (fold16Cells subtract j true) (fold16Input j)
    (fold16_erase_geometry subtract j hj) s m (fold16_comparator_clean subtract j hj s.basis inv.1)
  rw [(erase_views subtract j hj).1,(erase_views subtract j hj).2]
  exact inv.2 j (by omega)

theorem fold16_erase_invariant (subtract : Bool) (j : Nat) (hj : j<4) (s : State) (m : List Bool)
    (inv : Fold16Invariant subtract (j+1) s.basis) :
    Fold16Invariant subtract j (run (fold16Erase subtract j) m s).basis := by
  rw [fold16_erase_run subtract j hj s m inv]
  constructor
  · intro i hi hij
    by_cases eq : i=j
    · subst i; simp [writeBit]
    · have away : (59+i : Wire)≠59+j := by dsimp only [Wire]; omega
      simpa only [writeBit,Function.update_of_ne away] using inv.1 i hi (by omega)
  · intro i hij
    apply (keeper_congr subtract i _ s.basis ?_ ?_ ?_ ?_).mpr (inv.2 i (by omega))
    · have away : (0 : Wire)≠59+j := by dsimp only [Wire]; omega
      simp only [writeBit,Function.update_of_ne away]
    · have away : (59+i : Wire)≠59+j := by dsimp only [Wire]; omega
      simp only [writeBit,Function.update_of_ne away]
    · by_cases hz : i=0
      · simp [fold16Input,hz]
      · have away : (59+i-1 : Wire)≠59+j := by dsimp only [Wire]; omega
        simp only [fold16Input,if_neg hz,Option.map_some,Option.getD_some,writeBit,Function.update_of_ne away]
    · apply regValue_congr
      intro q hq
      have bound := data_bound subtract i q hq
      have part := (fold16_partition i (by omega)).2
      have away : q≠59+j := by dsimp only [Wire] at *; omega
      simp only [writeBit,Function.update_of_ne away]

end ECDSAAdd.Arithmetic.Paper935
