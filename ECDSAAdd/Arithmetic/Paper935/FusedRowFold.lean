import ECDSAAdd.Arithmetic.CuccaroSignedSquareInverse

namespace ECDSAAdd.Arithmetic.Paper935

/-- engine.py:2948–2996, source pin 64b5a13a. Reference placement uses
high payload 0..23, low payload 24..279, borrowed zero word 280..535,
and carry root 536. The separate sign is not in this support. -/
def fusedFoldHigh : List Wire := List.range 24
def fusedFoldLow : List Wire := (List.range 256).map (24+·)
def fusedFoldWord : List Wire := (List.range 256).map (280+·)

/-- The six nonzero taps after the initial copy. Each accumulator has 25
bits; its one-bit operand padding is the immediately following zero bit. -/
def fusedFoldTaps : List Nat := [4,6,7,8,9,32]
def fusedFoldTap (j : Nat) : Program :=
  cuccaroAdd (fusedFoldHigh++[280+j+25])
    ((List.range 25).map (280+j+·)) 536

/-- engine.py:2971–2988. Build high*(2^32+977) with the author's tap order. -/
def fusedFoldBuild : Program :=
  copyRegister none fusedFoldHigh (fusedFoldWord.take 24) ++
    fusedFoldTaps.flatMap fusedFoldTap

/-- engine.py:2989–2996. The subtraction is the literal reverse Cuccaro
stream, matching _cdkm_sub, rather than complement-add-complement. -/
def fusedRowFold (inverse : Bool) : Program :=
  fusedFoldBuild ++
    (if inverse then (cuccaroAdd fusedFoldWord fusedFoldLow 536).reverse
      else cuccaroAdd fusedFoldWord fusedFoldLow 536) ++
    fusedFoldBuild.reverse

theorem fusedFoldTap_proper (j : Nat) (hj : j∈fusedFoldTaps) :
    ProperProgram (fusedFoldTap j) := by
  apply cuccaroAdd_proper
  simp only [fusedFoldTaps,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem fusedFoldBuild_proper : ProperProgram fusedFoldBuild := by
  rw [fusedFoldBuild,properProgram_append]
  constructor
  · apply copyRegister_none_proper
    decide
  · intro i hi
    obtain ⟨j,hj,hi⟩ := List.mem_flatMap.mp hi
    exact fusedFoldTap_proper j hj i hi

theorem fusedRowFold_proper (inverse : Bool) : ProperProgram (fusedRowFold inverse) := by
  have central : ProperProgram (cuccaroAdd fusedFoldWord fusedFoldLow 536) :=
    cuccaroAdd_proper _ _ _ (by decide +kernel)
  rw [fusedRowFold,properProgram_append,properProgram_append]
  refine ⟨⟨fusedFoldBuild_proper,?_⟩,properProgram_reverse _ fusedFoldBuild_proper⟩
  cases inverse
  · exact central
  · exact properProgram_reverse _ central

theorem fusedRowFold_inverse : fusedRowFold true=(fusedRowFold false).reverse := by
  simp [fusedRowFold,List.reverse_append,List.append_assoc]

/-- Exact all-state round trip, including wrap lanes and dirty scratch.
Numeric reduction and scratch-zero postconditions require separate proofs. -/
theorem fusedRowFold_roundtrip (s : State) (m n : List Bool) :
    run (fusedRowFold true) n (run (fusedRowFold false) m s)=s := by
  rw [fusedRowFold_inverse]
  exact run_reverse_proper _ (fusedRowFold_proper false) s m n

theorem fusedFoldTap_counts (j : Nat) :
    toffoliCount (fusedFoldTap j)=48 ∧ measurementCount (fusedFoldTap j)=0 := by
  have h := cuccaroAdd_counts (fusedFoldHigh++[280+j+25])
    ((List.range 25).map (280+j+·)) 536 (by simp [fusedFoldHigh])
  simpa [fusedFoldTap] using h

theorem fusedRowFold_counts (inverse : Bool) :
    toffoliCount (fusedRowFold inverse)=1086 ∧ measurementCount (fusedRowFold inverse)=0 := by
  have cp := copyRegister_counts none fusedFoldHigh (fusedFoldWord.take 24)
    (by simp [fusedFoldHigh,fusedFoldWord])
  have add := cuccaroAdd_counts fusedFoldWord fusedFoldLow 536
    (by simp [fusedFoldWord,fusedFoldLow])
  have addCount : toffoliCount (cuccaroAdd fusedFoldWord fusedFoldLow 536)=510 := by
    simpa [fusedFoldLow] using add.1
  have build : toffoliCount fusedFoldBuild=288 ∧ measurementCount fusedFoldBuild=0 := by
    simp [fusedFoldBuild,fusedFoldTaps,cp,fusedFoldTap_counts]
  cases inverse <;> simp [fusedRowFold,toffoliCount_reverse,measurementCount_reverse,
    build,addCount,add.2]

theorem fusedFoldTap_support (j : Nat) (hj : j∈fusedFoldTaps) :
    wires (fusedFoldTap j) ⊆ Finset.range 537 := by
  apply Finset.Subset.trans (cuccaroAdd_wires_subset _ _ _)
  simp only [fusedFoldTaps,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

theorem fusedFoldBuild_support : wires fusedFoldBuild ⊆ Finset.range 537 := by
  have cp : wires (copyRegister none fusedFoldHigh (fusedFoldWord.take 24)) ⊆
      Finset.range 537 := by
    rw [copyRegister_wires _ _ _ (by simp [fusedFoldHigh,fusedFoldWord])]
    decide +kernel
  simp only [fusedFoldBuild,fusedFoldTaps,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,wires_append,Finset.union_subset_iff]
  exact ⟨cp,⟨fusedFoldTap_support 4 (by decide),⟨fusedFoldTap_support 6 (by decide),
    ⟨fusedFoldTap_support 7 (by decide),⟨fusedFoldTap_support 8 (by decide),
      ⟨fusedFoldTap_support 9 (by decide),fusedFoldTap_support 32 (by decide)⟩⟩⟩⟩⟩⟩

theorem fusedRowFold_support (inverse : Bool) :
    wires (fusedRowFold inverse) ⊆ Finset.range 537 := by
  have central : wires (cuccaroAdd fusedFoldWord fusedFoldLow 536) ⊆ Finset.range 537 := by
    apply Finset.Subset.trans (cuccaroAdd_wires_subset _ _ _)
    decide +kernel
  cases inverse <;> simpa [fusedRowFold,wires_reverse,Finset.union_subset_iff]
    using And.intro fusedFoldBuild_support (And.intro central fusedFoldBuild_support)

end ECDSAAdd.Arithmetic.Paper935
