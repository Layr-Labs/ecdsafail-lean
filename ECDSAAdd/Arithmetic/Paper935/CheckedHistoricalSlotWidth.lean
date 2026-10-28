import ECDSAAdd.Arithmetic.Paper935.HistoricalSlotWidth
import ECDSAAdd.Arithmetic.Paper935.CheckedHistoricalSlot

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.RecordedQuantum

def compileCheckedHistoricalSlotWidth (historyWidth : Nat) (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) : Option HistoricalSlot := do
  let Q ← compileHistoricalSlotWidth historyWidth A b record addWidth exitWidth F armed probeWidth offset capacity
  if Q.history.program.all historyInstructionCheck=true ∧ recordedWires Q.history.program⊆arenaWires
  then some Q else none

theorem compileCheckedHistoricalSlotWidth_contract (historyWidth : Nat) (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileCheckedHistoricalSlotWidth historyWidth A b record addWidth exitWidth F armed probeWidth offset capacity=some Q) :
    compileHistoricalSlotWidth historyWidth A b record addWidth exitWidth F armed probeWidth offset capacity=some Q ∧
    PhysicalProgram Q.history.program ∧ recordedWires Q.history.program⊆arenaWires := by
  unfold compileCheckedHistoricalSlotWidth at h
  obtain ⟨R,hr,h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next valid =>
    cases h
    refine ⟨hr,?_,valid.2⟩
    intro i hi
    exact (historyInstructionCheck_iff i).mp ((List.all_eq_true.mp valid.1) i hi)
  next invalid => simp at h

theorem compileCheckedHistoricalSlotWidth_resources (historyWidth : Nat) (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileCheckedHistoricalSlotWidth historyWidth A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (ordinal : Nat) :
    PhysicalProgram (Q.program F) ∧ recordedWires (Q.program F)⊆arenaWires ∧
    RecordedWellFormedAt ordinal (Q.program F) := by
  have hc := compileCheckedHistoricalSlotWidth_contract historyWidth A b record addWidth exitWidth F armed probeWidth offset capacity Q h
  have hs := (compileHistoricalSlotWidth_contract historyWidth A b record addWidth exitWidth F armed probeWidth offset capacity Q hc.1).1
  have resources := compileCheckedPublicSlot_resources A b addWidth exitWidth F armed probeWidth offset Q.slot hs
  refine ⟨?_,?_,?_⟩
  · rw [HistoricalSlot.program,physical_append,physical_embed]
    exact ⟨resources.1.1,hc.2.1⟩
  · rw [HistoricalSlot.program,recordedWires_append,embedRecorded_wires]
    exact Finset.union_subset resources.2.1 hc.2.2
  · rw [HistoricalSlot.program,RecordedWellFormedAt_append]
    exact ⟨embedRecorded_wellFormed _ _,storePushForget_wellFormed _ _ _ _ _ _ _ _ _ _ _ _⟩

end ECDSAAdd.Arithmetic.Paper935
