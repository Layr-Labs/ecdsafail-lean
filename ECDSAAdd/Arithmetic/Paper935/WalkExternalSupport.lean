import ECDSAAdd.Arithmetic.Paper935.HistoryExternalSupport
import ECDSAAdd.Arithmetic.Paper935.DecoderExternalSupport
import ECDSAAdd.Arithmetic.Paper935.WalkReverseArena
import ECDSAAdd.Arithmetic.Paper935.CloserResources

namespace ECDSAAdd.Arithmetic.Paper935

/-- Actual forward and reverse history compilers preserve a pre-owned external
wire syntactically, and retain its allocation at the final bank. -/
theorem HistoricalWalkCompiled.external_support (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : HistoricalWalkCompiled F probeWidth A b record requests slots)
    (p : Int) (index ordinal : Nat) (q : Wire) (owned : q∈A.live)
    (noMeta : q∉F.wires) (noRows : q∉b.rows.flatMap WindowRow.wires) (noRecord : q∉record) :
    q∈(walkExitArena A slots).live ∧ q∉(walkExitBank b slots).rows.flatMap WindowRow.wires ∧
    q∉recordedWires (historicalWalkProgram F slots) ∧
    q∉recordedWires (historicalWalkReverse F (actualHistoryDecoder F p) index ordinal slots) := by
  induction compiled generalizing index ordinal with
  | nil => exact ⟨owned,noRows,by simp [historicalWalkProgram,recordedWires],by simp [historicalWalkReverse,recordedWires]⟩
  | cons A b record r rs Q rest head tail ih =>
    have raw := (compileCheckedHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ head).1
    have step := compileHistoricalSlot_external_support _ _ _ _ _ _ _ _ _ _ _ raw q owned noMeta noRows noRecord
    have restFrame := ih (index+1) (ordinal+recordedMeasurementCount (Q.program F)) step.1 step.2.1 step.2.2.1
    have slot := compileHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ raw
    have hist := compileGrowingHistory_contract _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ slot.2.2.2.2.2
    have port := (compileHistory_identity _ _ _ _ _ _ _ _ _ _ _ _ hist.2.2).2.2.2.2.2
    have decoder := actualHistoryDecoder_external_support F Q port p index q step.1 noMeta step.2.1
    have histAway : q∉recordedWires Q.history.program := by
      intro hq
      apply step.2.2.2.1
      rw [HistoricalSlot.program,recordedWires_append]
      exact Finset.mem_union_right _ hq
    refine ⟨restFrame.1,restFrame.2.1,?_,?_⟩
    · change q∉recordedWires (Q.program F++historicalWalkProgram F rest)
      simpa only [recordedWires_append,Finset.mem_union,not_or] using And.intro step.2.2.2.1 restFrame.2.2.1
    · simpa only [historicalWalkReverse,HistoricalSlot.undo,recordedWires_append,
        HistoryLayout.recovery_support,embedRecorded_wires,Finset.mem_union,not_or] using
        And.intro restFrame.2.2.2 (And.intro (And.intro decoder histAway) step.2.2.2.2)

/-- The 256-site retained host is owned before seeding and lies outside every
seed row and walk register. -/
theorem aHost_seed_external (q : Wire) (hq : q∈aHost) :
    q∈walkSeedArena.live ∧ q∉walkRegisters.wires ∧ q∉walkSeedBank.rows.flatMap WindowRow.wires := by
  simp only [aHost,Finset.mem_Ico] at hq
  dsimp only [Wire] at *
  constructor
  · simp only [walkSeedArena,Finset.mem_range]; omega
  constructor
  · simp only [walkRegisters,SlotRegisters.wires,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,List.mem_range']
    omega
  · simp only [walkSeedBank,WindowBank.rows,WindowRow.wires,seedF,seedG,List.flatMap_cons,
      List.flatMap_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range,List.mem_range']
    omega

theorem compileAuthorWalk_aHost_external (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (p : Nat) (ordinal : Nat) (q : Wire) (hq : q∈aHost) :
    q∈(walkExitArena walkSeedArena slots).live ∧
    q∉(walkExitBank walkSeedBank slots).rows.flatMap WindowRow.wires ∧
    q∉recordedWires (historicalWalkProgram walkRegisters slots) ∧
    q∉recordedWires (historicalWalkReverse walkRegisters (actualHistoryDecoder walkRegisters p) 0 ordinal slots) := by
  have init := aHost_seed_external q hq
  exact (compileHistoricalWalk_contract _ _ _ _ _ _ _ compiled).external_support
    _ _ _ _ _ _ _ p 0 ordinal q init.1 init.2.1 init.2.2 (by simp)

end ECDSAAdd.Arithmetic.Paper935
