import ECDSAAdd.Arithmetic.Paper935.AllocationSupport

namespace ECDSAAdd.Arithmetic.Paper935

private theorem historyGrow_live (A B : Arena) (record grown : List Wire) (capacity : Nat)
    (h : planHistoryGrow A record capacity=some (B,grown)) : A.live⊆B.live := by
  unfold planHistoryGrow at h
  obtain ⟨⟨C,extra⟩,borrow,h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  rw [(A.borrowMany_live B _ extra borrow).1]
  exact Finset.subset_union_left

/-- Any owned site which disappears across a historical slot is touched by its
arithmetic inverse. The same accounts for its full counter allocation. -/
theorem compileHistoricalSlot_live_support (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (compiled : compileCheckedHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (nonempty : 1≤F.counter.length) :
    A.live⊆Q.historyArena.live∪wires (Q.slot.inverse F) ∧
    Q.slot.front.counterArena.live⊆Q.historyArena.live∪wires (Q.slot.inverse F) := by
  have raw := (compileCheckedHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ compiled).1
  have slot := compileHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ raw
  have pub := (compileCheckedPublicSlot_contract _ _ _ _ _ _ _ _ _ slot.1).1
  have front := compilePublicSlot_front _ _ _ _ _ _ _ _ _ pub
  have frontCoverage := (compileSlotFront_contract _ _ _ _ _ _ front).live_support _ _ _ _ _ _ nonempty
  have history := compileGrowingHistory_contract _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ slot.2.2.2.2.2
  have historyMono := historyGrow_live _ _ _ _ _ history.1
  have lift (S : Finset Wire) (coverage : S⊆Q.slot.front.exitArena.live∪wires (Q.slot.front.inverse F)) :
      S⊆Q.historyArena.live∪wires (Q.slot.inverse F) := by
    intro q hq
    rcases Finset.mem_union.mp (coverage hq) with live | touched
    · exact Finset.mem_union_left _ (historyMono live)
    · apply Finset.mem_union_right
      rw [PublicSlot.inverse,wires_append]
      exact Finset.mem_union_right _ touched
  exact ⟨lift _ frontCoverage.1,lift _ frontCoverage.2⟩

private theorem coverage_trans (A B C I J : Finset Wire)
    (first : A⊆B∪I) (second : B⊆C∪J) : A⊆C∪(J∪I) := by
  intro q hq
  rcases Finset.mem_union.mp (first hq) with live | touched
  · rcases Finset.mem_union.mp (second live) with live | touched
    · exact Finset.mem_union_left _ live
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ touched)
  · exact Finset.mem_union_right _ (Finset.mem_union_right _ touched)

/-- Coverage of entry ownership and every counter arena by final ownership or
actual reverse support. The decoder is arbitrary: arithmetic already covers
all disappearing and counter sites. -/
theorem HistoricalWalkCompiled.reverse_coverage (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : HistoricalWalkCompiled F probeWidth A b record requests slots)
    (nonempty : 1≤F.counter.length) (decoder : Nat → HistoricalSlot → Program) (index ordinal : Nat) :
    A.live⊆(walkExitArena A slots).live∪recordedWires (historicalWalkReverse F decoder index ordinal slots) ∧
    (∀ Q∈slots,Q.slot.front.counterArena.live⊆(walkExitArena A slots).live∪
      recordedWires (historicalWalkReverse F decoder index ordinal slots)) := by
  induction compiled generalizing index ordinal with
  | nil =>
    constructor
    · exact Finset.subset_union_left
    · simp
  | cons A b record r rs Q rest head tail ih =>
    have step := compileHistoricalSlot_live_support _ _ _ _ _ _ _ _ _ _ _ head nonempty
    have restCoverage := ih (index+1) (ordinal+recordedMeasurementCount (Q.program F))
    have localSub : wires (Q.slot.inverse F)⊆recordedWires (Q.undo F (decoder index Q) ordinal) := by
      rw [HistoricalSlot.undo,recordedWires_append,embedRecorded_wires]
      exact Finset.subset_union_right
    have localCoverage (S : Finset Wire) (h : S⊆Q.historyArena.live∪wires (Q.slot.inverse F)) :
        S⊆(walkExitArena A (Q::rest)).live∪
          recordedWires (historicalWalkReverse F decoder index ordinal (Q::rest)) := by
      have both := coverage_trans _ _ _ _ _ h restCoverage.1
      rw [walkExitArena,historicalWalkReverse,recordedWires_append]
      exact both.trans (Finset.union_subset_union Finset.Subset.rfl
        (Finset.union_subset_union Finset.Subset.rfl localSub))
    refine ⟨localCoverage _ step.1,?_⟩
    intro P hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact localCoverage _ step.2
    · rw [walkExitArena,historicalWalkReverse,recordedWires_append]
      exact (restCoverage.2 P hp).trans (Finset.union_subset_union Finset.Subset.rfl Finset.subset_union_left)

/-- The actual reverse plus the final live allocation covers every arena site.
A scalar-certified full counter arena is the witness, without enumerating gates. -/
theorem compileAuthorWalk_reverse_covers (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) :
    arenaWires⊆(walkExitArena walkSeedArena slots).live∪
      recordedWires (seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots) := by
  have wc := compileHistoricalWalk_contract walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests slots compiled
  have coverage := wc.reverse_coverage _ _ _ _ _ _ _ (by decide)
    (actualHistoryDecoder walkRegisters p) 0 ordinal
  obtain ⟨Q,hQ,full⟩ := compileAuthorWalk_counter_full slots compiled
  have covered := coverage.2 Q hQ
  rw [full] at covered
  rw [seededAuthorWalkReverse,recordedWires_append]
  exact covered.trans (Finset.union_subset_union Finset.Subset.rfl Finset.subset_union_left)

theorem retainedOutputSpace_empty (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) : retainedOutputSpace p ordinal slots=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have arena := (Finset.mem_sdiff.mp hq).1
  have apart := (Finset.mem_sdiff.mp hq).2
  rcases Finset.mem_union.mp (compileAuthorWalk_reverse_covers p ordinal slots compiled arena) with live | touched
  · exact apart (Finset.mem_union_left _ live)
  · apply apart
    apply Finset.mem_union_right
    rw [recordedWires_append]
    exact Finset.mem_union_right _ touched

theorem retainedOutputSpace_card_zero (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) : (retainedOutputSpace p ordinal slots).card=0 := by
  rw [retainedOutputSpace_empty p ordinal slots compiled,Finset.card_empty]

/-- The fresh-output contract can only be instantiated by the empty set for
this compiled walk. This says nothing about already-owned output hosts. -/
theorem retainedOutputSet_empty (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) (O : Finset Wire)
    (within : O⊆retainedOutputSpace p ordinal slots) : O=∅ := by
  rw [retainedOutputSpace_empty p ordinal slots compiled] at within
  exact Finset.subset_empty.mp within

end ECDSAAdd.Arithmetic.Paper935
