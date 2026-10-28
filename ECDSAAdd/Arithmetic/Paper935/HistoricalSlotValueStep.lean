import ECDSAAdd.Arithmetic.Paper935.HistoryValueGeometry
import ECDSAAdd.Arithmetic.Paper935.BankFrame

namespace ECDSAAdd.Arithmetic.Paper935

/-- The measured history stage restores input-format metadata, preserves the
mathematical rows and updates the actual stack integer. All frame and growth
conditions are derived from the actual compiled layout and allocator readiness. -/
theorem compileHistoricalSlot_value_step (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (compiled : compileCheckedHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (distinct : (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.slot.front.exitArena.live)
    (old next : PinState) (s : State) (values : F.OutputValues s.basis old next)
    (rows : Q.slot.front.exitBank.Encodes s.basis next.rows) (ready : Q.slot.front.exitArena.Ready s.basis)
    (fit : Q.history.selected s.basis=true →
      2*regValue record s.basis+(s.basis F.parity).toNat<2^(max capacity record.length))
    (m : List Bool) (ordinal : Nat) :
    let t := runWithTape Q.history.program m ordinal s
    F.Values t.basis next ∧ Q.historyArena.Ready t.basis ∧ Q.slot.front.exitBank.Encodes t.basis next.rows ∧
    regValue Q.history.record t.basis=(if Q.history.selected s.basis then
      2*regValue record s.basis+(s.basis F.parity).toNat else regValue record s.basis) := by
  have hc := (compileCheckedHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q compiled).1
  have slot := compileHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q hc
  have history := compileGrowingHistory_contract Q.slot.front.exitArena Q.historyArena Q.detectorArena record Q.detectorWork
    capacity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen F.counter
    (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history slot.2.2.2.2.2
  have ids := compileHistory_identity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen F.counter
    (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history.record Q.detectorWork Q.history history.2.2
  have inputGeometry := historyValue_geometry Q.slot.front.exitArena F Q.slot.front.exitBank record distinct owned
  have grown := compileHistoricalSlot_exit_geometry A b record addWidth exitWidth F armed probeWidth offset capacity Q
    compiled distinct owned
  have outputGeometry := historyValue_geometry Q.historyArena F Q.slot.front.exitBank Q.history.record grown.1 grown.2.1
  have growth := planHistoryGrow_correct Q.slot.front.exitArena Q.historyArena record Q.history.record capacity history.1
    inputGeometry.1 inputGeometry.2.1 s.basis ready
  have actualFit : Q.history.selected s.basis=true →
      2*regValue Q.history.record s.basis+(s.basis Q.history.port).toNat<2^Q.history.record.length := by
    simpa only [growth.1,growth.2.2.2.2.1,ids.2.2.2.2.2] using fit
  have result := compileHistoricalSlot_history_run A b record addWidth exitWidth F armed probeWidth offset capacity Q hc
    old next s values ready inputGeometry.1 inputGeometry.2.1 outputGeometry.2.2.1
    (by simpa only [ids.2.2.2.2.2] using outputGeometry.2.2.2.1) actualFit m ordinal
  refine ⟨result.1,result.2.1,?_,result.2.2.2.1⟩
  exact rows.frame Q.slot.front.exitBank s.basis _ next.rows (fun q hq => result.2.2.2.2 q
    (by simpa only [ids.2.2.2.2.2] using outputGeometry.2.2.2.2 q hq))

end ECDSAAdd.Arithmetic.Paper935
