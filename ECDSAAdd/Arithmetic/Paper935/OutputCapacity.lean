import ECDSAAdd.Arithmetic.Paper935.EndpointSlotAssembly

namespace ECDSAAdd.Arithmetic.Paper935

/-- Addresses that remain free at exit and untouched by the complete return
program. Exit freedom alone does not certify this stronger property. -/
def retainedOutputSpace (p ordinal : Nat) (slots : List HistoricalSlot) : Finset Wire :=
  arenaWires \ ((walkExitArena walkSeedArena slots).live ∪
    recordedWires (embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p).reverse ++
      seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots))

private theorem free_minus_return (A L R : Finset Wire) (rsub : R⊆A) :
    (A\(L∪R)).card=(A\L).card-(R\L).card := by
  have sub : R\L⊆A\L := by
    intro q hq
    exact Finset.mem_sdiff.mpr ⟨rsub (Finset.mem_sdiff.mp hq).1,(Finset.mem_sdiff.mp hq).2⟩
  have eqs : A\(L∪R)=(A\L)\(R\L) := by
    ext q
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [eqs,Finset.card_sdiff_of_subset sub]

/-- Exact accounting: each return-program wire outside the exit live set
removes one of the 28 exit-free sites. This is not a claim that all 28 survive. -/
theorem retainedOutputSpace_card (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) :
    (retainedOutputSpace p ordinal slots).card = 28 -
      (recordedWires (embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p).reverse ++
        seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots) \
        (walkExitArena walkSeedArena slots).live).card := by
  have bound : recordedWires (embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p).reverse ++
      seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots)⊆arenaWires := by
    rw [recordedWires_append,embedRecorded_wires,wires_reverse]
    exact Finset.union_subset
      (closerProgram_arena _ p _ (compileAuthorWalk_exit_owned slots compiled))
      (seededAuthorWalkReverse_support p ordinal slots compiled)
  rw [retainedOutputSpace,free_minus_return _ _ _ bound,compileAuthorWalk_free_card slots compiled]

/-- Already the persistent exit allocation limits this space to 28 bits;
intersecting with return-program isolation can only reduce it. -/
theorem retainedOutputSpace_card_le (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) :
    (retainedOutputSpace p ordinal slots).card≤28 := by
  have sub : retainedOutputSpace p ordinal slots⊆arenaWires\(walkExitArena walkSeedArena slots).live := by
    intro q hq
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hq).1,
      fun h => (Finset.mem_sdiff.mp hq).2 (Finset.mem_union_left _ h)⟩
  have bound := Finset.card_le_card sub
  rw [compileAuthorWalk_free_card slots compiled] at bound
  exact bound

theorem retainedOutputSpace_no_word (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) (O : Finset Wire)
    (within : O⊆retainedOutputSpace p ordinal slots) : O.card<256 :=
  lt_of_le_of_lt ((Finset.card_le_card within).trans (retainedOutputSpace_card_le p ordinal slots compiled)) (by decide)

end ECDSAAdd.Arithmetic.Paper935
