import ECDSAAdd.Arithmetic.Paper935.CheckedHistoricalSlotWidth
import ECDSAAdd.Arithmetic.Paper935.HistoryCompilerLengths

namespace ECDSAAdd.Arithmetic.Paper935

theorem compileHistoricalSlotWidth_lengths (hw : Nat) (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileHistoricalSlotWidth hw A b record addWidth exitWidth F armed probeWidth offset capacity=some Q) :
    Q.history.record.length=max capacity record.length ∧ Q.history.low.length+1=hw+1 := by
  have hc := compileHistoricalSlotWidth_contract hw A b record addWidth exitWidth F armed probeWidth offset capacity Q h
  have hh := compileGrowingHistory_contract Q.slot.front.exitArena Q.historyArena Q.detectorArena record
    Q.detectorWork capacity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take hw) Q.history hc.2.2.2.2.2
  have views := compileHistory_contract F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take hw) Q.history.record Q.detectorWork Q.history hh.2.2
  have len := congrArg List.length views.2.2.1
  simp only [List.length_map,hc.2.2.2.1] at len
  exact ⟨planHistoryGrow_length _ _ _ _ _ hh.1,by omega⟩

end ECDSAAdd.Arithmetic.Paper935
