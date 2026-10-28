import ECDSAAdd.Arithmetic.Paper935.EndpointSlot
import ECDSAAdd.Arithmetic.Paper935.SeededWalkResources

namespace ECDSAAdd.Arithmetic.Paper935

private theorem splice_support (W R E : RecordedProgram) (C : Program)
    (w : recordedWires W⊆arenaWires) (r : recordedWires R⊆arenaWires)
    (e : recordedWires E⊆arenaWires) (c : wires C⊆arenaWires) :
    recordedWires (W++embedRecorded C++E++embedRecorded C.reverse++R)⊆arenaWires := by
  simp only [recordedWires_append,embedRecorded_wires,wires_reverse]
  exact Finset.union_subset (Finset.union_subset (Finset.union_subset (Finset.union_subset w c) e) c) r

theorem endpointSlot_support (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) (E : RecordedProgram) (arena : recordedWires E⊆arenaWires) :
    recordedWires (endpointSlotProgram p ordinal slots E)⊆arenaWires :=
  splice_support _ _ _ _ (seededAuthorWalk_support p slots compiled)
    (seededAuthorWalkReverse_support p ordinal slots compiled) arena
    (closerProgram_arena _ p _ (compileAuthorWalk_exit_owned slots compiled))

theorem endpointSlot_address_bound (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) (E : RecordedProgram) (arena : recordedWires E⊆arenaWires) :
    ∀ q∈recordedWires (endpointSlotProgram p ordinal slots E),q<935 := by
  intro q hq
  exact Finset.mem_range.mp (endpointSlot_support p ordinal slots compiled E arena hq)

private theorem splice_wellFormed (W R E : RecordedProgram) (C : Program) (k : Nat)
    (hm : measurementCount C=0) (w : RecordedWellFormedAt k W)
    (e : RecordedWellFormedAt (k+recordedMeasurementCount W) E)
    (r : RecordedWellFormedAt (k+recordedMeasurementCount W+recordedMeasurementCount E) R) :
    RecordedWellFormedAt k (W++embedRecorded C++E++embedRecorded C.reverse++R) := by
  simp only [RecordedWellFormedAt_append,recordedMeasurementCount_append,
    (embedRecorded_counts _).2,measurementCount_reverse,hm,Nat.add_zero,←Nat.add_assoc]
  exact ⟨⟨⟨⟨w,embedRecorded_wellFormed _ _⟩,e⟩,embedRecorded_wellFormed _ _⟩,r⟩

theorem endpointSlot_wellFormed (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) (E : RecordedProgram)
    (wellFormed : RecordedWellFormedAt (endpointCursor p ordinal slots) E) :
    RecordedWellFormedAt ordinal (endpointSlotProgram p ordinal slots E) :=
  splice_wellFormed _ _ _ _ ordinal (closerProgram_counts _ _).2
    (seededAuthorWalk_wellFormed p ordinal slots compiled) wellFormed
    (seededAuthorWalkReverse_wellFormed p ordinal _ slots (Nat.le_add_right _ _))

/-- E's promised transaction really borrows only the 315 free sites, reserves
inside the same arena, and releases its actual output back to the closed arena.
This does not select the borrowed sites or certify E without its contract. -/
theorem endpointBorrow_bounds (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (E : RecordedProgram) (out : State) (borrow : EndpointBorrow (authorClosedArena slots) E out) :
    ∃ qs : Finset Wire, ∃ during : Arena,
      qs⊆arenaWires\(authorClosedArena slots).live ∧
      (authorClosedArena slots).reserve qs=some during ∧
      recordedWires E⊆during.live ∧ during.release qs out.basis=some (authorClosedArena slots) ∧
      qs.card≤315 ∧ during.live.card≤935 := by
  obtain ⟨qs,during,free,reserved,support,released⟩ := borrow
  refine ⟨qs,during,free,reserved,support,released,?_,during.peak_bound⟩
  have bound := Finset.card_le_card free
  rw [compileAuthorWalk_closed_free slots compiled] at bound
  exact bound

end ECDSAAdd.Arithmetic.Paper935
