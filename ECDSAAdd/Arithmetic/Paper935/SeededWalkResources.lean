import ECDSAAdd.Arithmetic.Paper935.WalkReverseArena

namespace ECDSAAdd.Arithmetic.Paper935

private theorem seedRows_arena (p : Nat) : wires (seedRows p)⊆arenaWires := by
  apply (seed_support p).trans
  intro q hq
  simp only [seedBorrowed,yHost,Finset.mem_union,Finset.mem_Ico,arenaWires,Finset.mem_range] at hq ⊢
  dsimp only [Wire] at *
  omega

private theorem seedMetadata_arena : wires seedWalkMetadata⊆arenaWires := by
  simp [seedWalkMetadata,wires,Instr.wires,arenaWires]

theorem seededAuthorWalk_support (p : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) :
    recordedWires (seededAuthorWalkProgram p slots)⊆arenaWires := by
  have contract := compileHistoricalWalk_contract walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests slots compiled
  rw [seededAuthorWalkProgram,recordedWires_append,embedRecorded_wires,seedWalk,wires_append]
  exact Finset.union_subset (Finset.union_subset (seedRows_arena p) seedMetadata_arena)
    (contract.resources _ _ _ _ _ _ _ 0).2.1

theorem seededAuthorWalkReverse_support (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) :
    recordedWires (seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots)⊆arenaWires := by
  rw [seededAuthorWalkReverse,recordedWires_append,embedRecorded_wires,unseedWalk,wires_append]
  exact Finset.union_subset (compileAuthorWalk_reverse_support p slots compiled ordinal)
    (Finset.union_subset seedMetadata_arena (seedRows_arena p))

theorem seededAuthorWalk_wellFormed (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) :
    RecordedWellFormedAt ordinal (seededAuthorWalkProgram p slots) := by
  have contract := compileHistoricalWalk_contract walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests slots compiled
  rw [seededAuthorWalkProgram,RecordedWellFormedAt_append]
  exact ⟨embedRecorded_wellFormed _ _,(contract.resources _ _ _ _ _ _ _ _).2.2⟩

theorem seededAuthorWalkReverse_wellFormed (p ordinal cursor : Nat) (slots : List HistoricalSlot)
    (past : ordinal+recordedMeasurementCount (seededAuthorWalkProgram p slots)≤cursor) :
    RecordedWellFormedAt cursor (seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots) := by
  rw [seededAuthorWalkReverse,RecordedWellFormedAt_append]
  refine ⟨historicalWalkReverse_wellFormed _ _ _ _ _ _ ?_,embedRecorded_wellFormed _ _⟩
  simpa only [seededAuthorWalkProgram,recordedMeasurementCount_append,(embedRecorded_counts _).2,
    seedWalk_measurements,Nat.zero_add] using past

end ECDSAAdd.Arithmetic.Paper935
