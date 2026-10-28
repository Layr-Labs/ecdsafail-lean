import ECDSAAdd.Arithmetic.Paper935.HistoricalSlotRun

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.RecordedQuantum

/-- A computable address check on the emitted instruction, independent of
input values or the success event. -/
def historyInstructionCheck : RecordedInstr → Bool
  | .gate (.X _) => true
  | .gate (.CX c t) => decide (c≠t)
  | .gate (.CCX a b t) => decide (a≠t ∧ b≠t)
  | .gate (.measureX _ _ _) => true
  | .phaseFromRecord _ _ => true

theorem historyInstructionCheck_iff (i : RecordedInstr) :
    historyInstructionCheck i=true ↔ PhysicalInstr i := by
  cases i with
  | gate i => cases i <;> simp [historyInstructionCheck,PhysicalInstr,ProperGate]
  | phaseFromRecord => simp [historyInstructionCheck,PhysicalInstr]

def compileCheckedHistoricalSlot (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) : Option HistoricalSlot := do
  let Q ← compileHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity
  if Q.history.program.all historyInstructionCheck=true ∧ recordedWires Q.history.program⊆arenaWires
  then some Q else none

theorem compileCheckedHistoricalSlot_contract (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileCheckedHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q) :
    compileHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q ∧
    PhysicalProgram Q.history.program ∧ recordedWires Q.history.program⊆arenaWires := by
  unfold compileCheckedHistoricalSlot at h
  obtain ⟨R,hr,h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next valid =>
    cases h
    refine ⟨hr,?_,valid.2⟩
    intro i hi
    exact (historyInstructionCheck_iff i).mp ((List.all_eq_true.mp valid.1) i hi)
  next invalid => simp at h

theorem compileCheckedHistoricalSlot_resources (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileCheckedHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (ordinal : Nat) :
    PhysicalProgram (Q.program F) ∧ recordedWires (Q.program F)⊆arenaWires ∧
    RecordedWellFormedAt ordinal (Q.program F) := by
  have hc := compileCheckedHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q h
  have hs := (compileHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q hc.1).1
  have resources := compileCheckedPublicSlot_resources A b addWidth exitWidth F armed probeWidth offset Q.slot hs
  refine ⟨?_,?_,?_⟩
  · rw [HistoricalSlot.program,physical_append,physical_embed]
    exact ⟨resources.1.1,hc.2.1⟩
  · rw [HistoricalSlot.program,recordedWires_append,embedRecorded_wires]
    exact Finset.union_subset resources.2.1 hc.2.2
  · rw [HistoricalSlot.program,RecordedWellFormedAt_append]
    exact ⟨embedRecorded_wellFormed _ _,storePushForget_wellFormed _ _ _ _ _ _ _ _ _ _ _ _⟩

end ECDSAAdd.Arithmetic.Paper935
