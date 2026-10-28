import ECDSAAdd.Arithmetic.Paper935.HistoricalWalkCompiler

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.RecordedQuantum

def historicalWalkProgram (F : SlotRegisters) (slots : List HistoricalSlot) : RecordedProgram :=
  slots.flatMap (fun Q => Q.program F)

theorem HistoricalWalkCompiled.resources (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (h : HistoricalWalkCompiled F probeWidth A b record requests slots)
    (ordinal : Nat) :
    PhysicalProgram (historicalWalkProgram F slots) ∧
    recordedWires (historicalWalkProgram F slots)⊆arenaWires ∧
    RecordedWellFormedAt ordinal (historicalWalkProgram F slots) := by
  induction h generalizing ordinal with
  | nil => simp [historicalWalkProgram,PhysicalProgram,recordedWires,RecordedWellFormedAt]
  | cons A b record r rs Q rest head tail ih =>
    have hs := compileCheckedHistoricalSlot_resources A b record (bankWidths b).addPad
      (historyWindow r.exitWidth) F r.armed probeWidth r.offset r.capacity Q head ordinal
    have ht := ih (ordinal+recordedMeasurementCount (Q.program F))
    change PhysicalProgram (Q.program F++historicalWalkProgram F rest) ∧ _
    rw [physical_append]
    refine ⟨⟨hs.1,ht.1⟩,?_,?_⟩
    · change recordedWires (Q.program F++historicalWalkProgram F rest)⊆arenaWires
      rw [recordedWires_append]
      exact Finset.union_subset hs.2.1 ht.2.1
    · change RecordedWellFormedAt ordinal (Q.program F++historicalWalkProgram F rest)
      rw [RecordedWellFormedAt_append]
      exact ⟨hs.2.2,ht.2.2⟩

/-- Successful compilation gives a physical 935-address measured circuit for
the actual emitted walk. This does not assert compiler success on any schedule. -/
theorem compileHistoricalWalk_realize (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (h : compileHistoricalWalk F probeWidth A b record requests=some slots)
    (ordinal : Nat) :
    ∃ l, ∃ c : Circuit 935 ordinal l,c.program=historicalWalkProgram F slots := by
  have contract := compileHistoricalWalk_contract F probeWidth A b record requests slots h
  have resources := contract.resources F probeWidth A b record requests slots ordinal
  exact realize 935 ordinal _ resources.1 resources.2.2 resources.2.1

end ECDSAAdd.Arithmetic.Paper935
