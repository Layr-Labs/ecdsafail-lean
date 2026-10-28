import ECDSAAdd.Arithmetic.Paper935.FoldCompareBlock

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Author keeper erasure: complement the written sum, compare the constant
plus incoming carry, toggle the saved keeper, and restore the sum. -/
def foldKeeperErase (control keeper : Wire) (cells : List FoldCell) (cin : Option Wire) : Program :=
  notRegister (cells.map FoldCell.data) ++ foldCompareBlock control keeper cells cin ++
    notRegister (cells.map FoldCell.data)

private theorem separated_counts (cells : List FoldCell) (q : Wire) :
    (cells.flatMap FoldCell.wires).count q=(cells.map FoldCell.data).count q+(cells.map FoldCell.carry).count q := by
  induction cells with
  | nil => rfl
  | cons b rest ih =>
    simp only [List.flatMap_cons,FoldCell.wires,List.map_cons,List.count_append,List.count_cons,List.count_nil,ih]
    omega

theorem foldKeeperErase_run (control keeper : Wire) (cells : List FoldCell) (cin : Option Wire)
    (hn : ([control,keeper]++cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (s : State) (m : List Bool) (clean : ∀ b∈cells,s.basis b.carry=false) :
    run (foldKeeperErase control keeper cells cin) m s=
      ⟨s.phase,writeBit s.basis keeper (s.basis keeper ^^ (s.basis control &&
        decide (regValue (cells.map FoldCell.data) s.basis<
          foldBlockLiteral cells true+((cin.map s.basis).getD false).toNat)))⟩ := by
  have separated : ([control,keeper]++cin.toList++cells.map FoldCell.data++cells.map FoldCell.carry).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simpa only [List.count_append,separated_counts,Nat.add_assoc] using h
  obtain ⟨preNd,_,allApart⟩ := List.nodup_append'.mp separated
  obtain ⟨_,dataNd,preApart⟩ := List.nodup_append'.mp preNd
  have controlAway : control∉cells.map FoldCell.data :=
    List.disjoint_left.mp preApart (by simp)
  have keeperAway : keeper∉cells.map FoldCell.data :=
    List.disjoint_left.mp preApart (by simp)
  let complemented : BasisState := fun q => if q∈cells.map FoldCell.data then !s.basis q else s.basis q
  have ctrl : complemented control=s.basis control := by simp only [complemented,if_neg controlAway]
  have flag : complemented keeper=s.basis keeper := by simp only [complemented,if_neg keeperAway]
  have inp : (cin.map complemented).getD false=(cin.map s.basis).getD false := by
    cases hi : cin with
    | none => rfl
    | some q =>
      have hq : q∉cells.map FoldCell.data := List.disjoint_left.mp preApart (by simp [hi])
      simp only [Option.map_some,Option.getD_some,complemented,if_neg hq]
  have nextClean : ∀ b∈cells,complemented b.carry=false := by
    intro b hb
    have hq : b.carry∉cells.map FoldCell.data := by
      intro hd
      exact List.disjoint_left.mp allApart (by simp [hd]) (List.mem_map.mpr ⟨b,hb,rfl⟩)
    simpa only [complemented,if_neg hq] using clean b hb
  have value : regValue (cells.map FoldCell.data) complemented=
      2^cells.length-1-regValue (cells.map FoldCell.data) s.basis := by
    rw [regValue_congr (cells.map FoldCell.data) complemented (fun q => !s.basis q)
      (by intro q hq; simp only [complemented,if_pos hq]),regValue_complement,List.length_map]
  have borrow : foldBlockOverflow cells true ((cin.map complemented).getD false) complemented=
      decide (regValue (cells.map FoldCell.data) s.basis<foldBlockLiteral cells true+
        ((cin.map s.basis).getD false).toNat) := by
    apply Bool.eq_iff_iff.mpr
    rw [foldBlockOverflow_iff]
    simp only [decide_eq_true_eq,value,inp]
    have bound : regValue (cells.map FoldCell.data) s.basis<2^cells.length := by
      simpa only [List.length_map] using regValue_lt (cells.map FoldCell.data) s.basis
    omega
  have first (ms : List Bool) : run (notRegister (cells.map FoldCell.data)) ms s=⟨s.phase,complemented⟩ :=
    notRegister_correct _ dataNd s ms
  rw [foldKeeperErase,run_append,run_take,run_append,run_take,first,
    (notRegister_counts _).2,List.drop_zero]
  rw [foldCompareBlock_run control keeper cells cin hn ⟨s.phase,complemented⟩ m nextClean]
  rw [notRegister_correct _ dataNd]
  simp only [ctrl,flag,borrow]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=keeper
  · subst q
    simp only [if_neg keeperAway,writeBit,Function.update_self]
  · by_cases hd : q∈cells.map FoldCell.data <;>
      simp only [complemented,writeBit,Function.update_of_ne hq,hd,if_true,if_false,Bool.not_not]

/-- With the already proved keeper predicate, the physical comparator erases
that keeper and restores every other bit and the phase. -/
theorem foldKeeperErase_clean (control keeper : Wire) (cells : List FoldCell) (cin : Option Wire)
    (hn : ([control,keeper]++cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (s : State) (m : List Bool) (clean : ∀ b∈cells,s.basis b.carry=false)
    (known : s.basis keeper=(s.basis control && decide
      (regValue (cells.map FoldCell.data) s.basis<foldBlockLiteral cells true+
        ((cin.map s.basis).getD false).toNat))) :
    run (foldKeeperErase control keeper cells cin) m s=⟨s.phase,writeBit s.basis keeper false⟩ := by
  rw [foldKeeperErase_run control keeper cells cin hn s m clean,←known,Bool.xor_self]

theorem foldKeeperErase_counts (control keeper : Wire) (cells : List FoldCell) (cin : Option Wire) :
    toffoliCount (foldKeeperErase control keeper cells cin)≤cells.length+1 ∧
    measurementCount (foldKeeperErase control keeper cells cin)≤cells.length := by
  simpa only [foldKeeperErase,toffoliCount_append,measurementCount_append,
    (notRegister_counts _).1,(notRegister_counts _).2,Nat.zero_add,Nat.add_zero]
    using foldCompareBlock_counts control keeper cells cin

theorem foldKeeperErase_support (control keeper : Wire) (cells : List FoldCell) (cin : Option Wire) :
    wires (foldKeeperErase control keeper cells cin) ⊆
      ([control,keeper]++cin.toList++cells.flatMap FoldCell.wires).toFinset := by
  have dataSubset : (cells.map FoldCell.data).toFinset ⊆
      ([control,keeper]++cin.toList++cells.flatMap FoldCell.wires).toFinset := by
    intro q hq
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have h : b.data∈cells.flatMap FoldCell.wires := List.mem_flatMap.mpr ⟨b,hb,by simp [FoldCell.wires]⟩
    simp only [List.mem_toFinset,List.mem_append]
    exact Or.inr h
  rw [foldKeeperErase,wires_append,wires_append,notRegister_wires,
    Finset.union_subset_iff,Finset.union_subset_iff]
  exact ⟨⟨dataSubset,foldCompareBlock_support control keeper cells cin⟩,dataSubset⟩

theorem foldKeeperErase_physical (control keeper : Wire) (cells : List FoldCell) (cin : Option Wire)
    (hn : ([control,keeper]++cin.toList++cells.flatMap FoldCell.wires).Nodup) :
    GatePhysical (foldKeeperErase control keeper cells cin) := by
  rw [foldKeeperErase,gatePhysical_append,gatePhysical_append]
  exact ⟨⟨notRegister_physical _,foldCompareBlock_physical control keeper cells cin hn⟩,notRegister_physical _⟩

end ECDSAAdd.Arithmetic.Paper935
