import ECDSAAdd.Arithmetic.Paper935.Sign24Ready

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def Sign24Keeper (subtract : Bool) (j : Nat) (s : BasisState) : Prop :=
  s (59+j)=(s 0 && decide (regValue ((sign24Cells subtract j false).map FoldCell.data) s<
    foldBlockLiteral (sign24Cells subtract j false) true+(((sign24Input j).map s).getD false).toNat))

/-- Clean unoccupied pool plus exact predicates for every occupied keeper. -/
def Sign24Invariant (subtract : Bool) (j : Nat) (s : BasisState) : Prop :=
  Sign24Ready j s ∧ ∀ i<j,Sign24Keeper subtract i s

theorem sign24_forward_prefix (subtract : Bool) (j : Nat) (hj : j<3) (s : State) (m : List Bool)
    (ready : Sign24Ready j s.basis) (q : Wire)
    (before : q<1+sign24Starts[j]?.getD 0 ∨ (59≤q ∧ q<59+j)) :
    (run (sign24Forward subtract j) m s).basis q=s.basis q := by
  apply sign24_forward_frame subtract j hj s m ready q
  intro mem
  have bounds := sign24_cells_bounds subtract j false q mem
  have part := (sign24_partition j hj).2
  simp only [Bool.false_eq_true,if_false] at bounds
  dsimp only [Wire] at *
  omega

private theorem data_bound (subtract : Bool) (j : Nat) (q : Wire)
    (hq : q∈(sign24Cells subtract j false).map FoldCell.data) :
    1+sign24Starts[j]?.getD 0≤q ∧ q<1+sign24Starts[j]?.getD 0+sign24Sizes[j]?.getD 0 := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  have hi := List.mem_range.mp hi
  dsimp only [Wire]
  omega

private theorem blocks_order (i j : Nat) (hij : i<j) (hj : j<3) :
    sign24Starts[i]?.getD 0+sign24Sizes[i]?.getD 0≤sign24Starts[j]?.getD 0 := by
  have hi : i<3 := by omega
  interval_cases i <;> interval_cases j <;> simp_all [sign24Starts,sign24Sizes]

private theorem keeper_congr (subtract : Bool) (i : Nat) (s t : BasisState)
    (hc : s 0=t 0) (hk : s (59+i)=t (59+i))
    (hin : ((sign24Input i).map s).getD false=((sign24Input i).map t).getD false)
    (hd : regValue ((sign24Cells subtract i false).map FoldCell.data) s=
      regValue ((sign24Cells subtract i false).map FoldCell.data) t) :
    Sign24Keeper subtract i s ↔ Sign24Keeper subtract i t := by
  simp only [Sign24Keeper,hc,hk,hin,hd]

theorem sign24_forward_preserves_keeper (subtract : Bool) (i j : Nat) (hij : i<j) (hj : j<3)
    (s : State) (m : List Bool) (ready : Sign24Ready j s.basis)
    (known : Sign24Keeper subtract i s.basis) :
    Sign24Keeper subtract i (run (sign24Forward subtract j) m s).basis := by
  apply (keeper_congr subtract i _ s.basis ?_ ?_ ?_ ?_).mpr known
  · exact sign24_forward_prefix subtract j hj s m ready 0 (Or.inl (by dsimp only [Wire]; omega))
  · apply sign24_forward_prefix subtract j hj s m ready (59+i)
    right
    dsimp only [Wire]
    omega
  · by_cases hi : i=0
    · simp [sign24Input,hi]
    · simp only [sign24Input,if_neg hi,Option.map_some,Option.getD_some]
      apply sign24_forward_prefix subtract j hj s m ready (59+i-1)
      right
      dsimp only [Wire]
      omega
  · apply regValue_congr
    intro q hq
    have bound := data_bound subtract i q hq
    have order := blocks_order i j hij hj
    apply sign24_forward_prefix subtract j hj s m ready q
    left
    dsimp only [Wire] at *
    omega

theorem sign24_input_inactive (subtract : Bool) (j : Nat) (s : BasisState)
    (keepers : ∀ i<j,Sign24Keeper subtract i s) (off : s 0=false) :
    ((sign24Input j).map s).getD false=false := by
  by_cases hj : j=0
  · simp [sign24Input,hj]
  · have known := keepers (j-1) (by omega)
    have val : s (59+(j-1))=false := by simpa only [Sign24Keeper,off,Bool.false_and] using known
    simp only [sign24Input,if_neg hj,Option.map_some,Option.getD_some]
    rw [show (59+j-1 : Wire)=59+(j-1) by dsimp only [Wire]; omega]
    exact val

theorem sign24_forward_invariant (subtract : Bool) (j : Nat) (hj : j<2) (s : State) (m : List Bool)
    (inv : Sign24Invariant subtract j s.basis) :
    Sign24Invariant subtract (j+1) (run (sign24Forward subtract j) m s).basis := by
  refine ⟨sign24_forward_ready subtract j hj s m inv.1,?_⟩
  intro i hi
  by_cases old : i<j
  · exact sign24_forward_preserves_keeper subtract i j old (by omega) s m inv.1 (inv.2 i old)
  · have eq : i=j := by omega
    subst i
    have clean := sign24_forward_clean subtract j (by omega) s.basis inv.1
    have known := foldBlockSave_keeper 0 (sign24Top j) (sign24Saved subtract j) _ _
      (sign24_cells_geometry subtract j (by omega)) (sign24_saved_mem subtract j hj)
      (sign24_cells_top subtract j (by omega)) (sign24_top_distinct j hj) s m clean
      (sign24_input_inactive subtract j s.basis inv.2)
    have ctrl := sign24_forward_prefix subtract j (by omega) s m inv.1 0 (Or.inl (by dsimp only [Wire]; omega))
    have input : ((sign24Input j).map (run (sign24Forward subtract j) m s).basis).getD false=
        ((sign24Input j).map s.basis).getD false := by
      by_cases hz : j=0
      · simp [sign24Input,hz]
      · simp only [sign24Input,if_neg hz,Option.map_some,Option.getD_some]
        apply sign24_forward_prefix subtract j (by omega) s m inv.1 (59+j-1)
        right
        dsimp only [Wire]
        omega
    unfold Sign24Keeper
    rw [ctrl,input]
    simpa only [sign24Forward,if_pos hj,sign24Saved] using known

theorem sign24_last_invariant (subtract : Bool) (s : State) (m : List Bool)
    (inv : Sign24Invariant subtract 2 s.basis) :
    Sign24Invariant subtract 2 (run (sign24Forward subtract 2) m s).basis := by
  refine ⟨sign24_last_ready subtract s m inv.1,?_⟩
  intro i hi
  exact sign24_forward_preserves_keeper subtract i 2 hi (by decide) s m inv.1 (inv.2 i hi)

private theorem erase_views (subtract : Bool) (j : Nat) (hj : j<2) :
    (sign24Cells subtract j true).map FoldCell.data=(sign24Cells subtract j false).map FoldCell.data ∧
    foldBlockLiteral (sign24Cells subtract j true) true=foldBlockLiteral (sign24Cells subtract j false) true := by
  cases subtract <;> interval_cases j <;> decide

theorem sign24_erase_run (subtract : Bool) (j : Nat) (hj : j<2) (s : State) (m : List Bool)
    (inv : Sign24Invariant subtract (j+1) s.basis) :
    run (sign24Erase subtract j) m s=⟨s.phase,writeBit s.basis (59+j) false⟩ := by
  apply foldKeeperErase_clean 0 (59+j) (sign24Cells subtract j true) (sign24Input j)
    (sign24_erase_geometry subtract j hj) s m (sign24_comparator_clean subtract j hj s.basis inv.1)
  rw [(erase_views subtract j hj).1,(erase_views subtract j hj).2]
  exact inv.2 j (by omega)

theorem sign24_erase_invariant (subtract : Bool) (j : Nat) (hj : j<2) (s : State) (m : List Bool)
    (inv : Sign24Invariant subtract (j+1) s.basis) :
    Sign24Invariant subtract j (run (sign24Erase subtract j) m s).basis := by
  rw [sign24_erase_run subtract j hj s m inv]
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
      · simp [sign24Input,hz]
      · have away : (59+i-1 : Wire)≠59+j := by dsimp only [Wire]; omega
        simp only [sign24Input,if_neg hz,Option.map_some,Option.getD_some,writeBit,Function.update_of_ne away]
    · apply regValue_congr
      intro q hq
      have bound := data_bound subtract i q hq
      have part := (sign24_partition i (by omega)).2
      have away : q≠59+j := by dsimp only [Wire] at *; omega
      simp only [writeBit,Function.update_of_ne away]

end ECDSAAdd.Arithmetic.Paper935
