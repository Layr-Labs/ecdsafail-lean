import ECDSAAdd.Arithmetic.Paper935.PublicSlotMath
import ECDSAAdd.Arithmetic.Paper935.HistoryCompilerRelease

namespace ECDSAAdd.Arithmetic.Paper935

structure HistoricalSlot where
  slot : PublicSlot
  historyArena : Arena
  detectorArena : Arena
  detectorWork : List Wire
  history : HistoryLayout

def HistoricalSlot.program (P : HistoricalSlot) (F : SlotRegisters) : RecordedProgram :=
  embedRecorded (P.slot.program F) ++ P.history.program

/-- Append the actual growing history stage to the public arithmetic slot.
The six-bit coefficient view is taken from the physical exit row itself. -/
def compileHistoricalSlot (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) : Option HistoricalSlot := do
  let P ← compileCheckedPublicSlot A b addWidth exitWidth F armed probeWidth offset
  let vs := P.front.exitBank.fv.wires
  if F.counter=F.counter.dropLast++[F.counter.getLastD 0] ∧
      vs=vs.headD 0::(vs.drop 1 |>.take 6)++vs.drop 7 ∧
      (vs.drop 1 |>.take 6).length=6 ∧ vs.drop 7≠[] then
    let (B,D,work,H) ← compileGrowingHistory P.front.exitArena record capacity
      F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
      F.counter (vs.drop 1 |>.take 6)
    pure ⟨P,B,D,work,H⟩
  else none

theorem compileHistoricalSlot_contract (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q) :
    compileCheckedPublicSlot A b addWidth exitWidth F armed probeWidth offset=some Q.slot ∧
    F.counter=F.counter.dropLast++[F.counter.getLastD 0] ∧
    Q.slot.front.exitBank.fv.wires=Q.slot.front.exitBank.fv.wires.headD 0::
      (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6)++Q.slot.front.exitBank.fv.wires.drop 7 ∧
    (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6).length=6 ∧
    Q.slot.front.exitBank.fv.wires.drop 7≠[] ∧
    compileGrowingHistory Q.slot.front.exitArena record capacity F.one F.work0 F.work1
      (F.counter.getLastD 0) F.active F.parity F.frozen F.counter
      (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6)=
        some (Q.historyArena,Q.detectorArena,Q.detectorWork,Q.history) := by
  unfold compileHistoricalSlot at h
  obtain ⟨P,hp,h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  next views =>
    obtain ⟨⟨B,D,work,H⟩,hh,h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact ⟨hp,views.1,views.2.1,views.2.2.1,views.2.2.2,hh⟩
  next invalid => simp at h

theorem compileHistoricalSlot_depth_capacity (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (s : BasisState) (ready : Q.slot.front.exitArena.Ready s)
    (hn : record.Nodup) (owned : record.toFinset⊆Q.slot.front.exitArena.live) :
    Q.history.low.length+1=7 ∧ Q.history.record.length=max capacity record.length := by
  have hc := compileHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q h
  have grow := compileGrowingHistory_capacity Q.slot.front.exitArena Q.historyArena Q.detectorArena record
    Q.detectorWork capacity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history hc.2.2.2.2.2 hn owned s ready
  exact ⟨by rw [grow.2.1,hc.2.2.2.1],grow.1⟩

/-- Bind the compiled store selector to the same post-slot state produced by
compileCheckedPublicSlot_run, with no guessed coefficient/register mapping. -/
theorem compileHistoricalSlot_selector (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (old next : PinState) (s : BasisState) (values : F.OutputValues s old next)
    (rows : Q.slot.front.exitBank.Encodes s next.rows)
    (p : Int) (inv : ECDSAAdd.Divsteps.Inv p next.rows) :
    Q.history.selected s=(!next.frozen && decide (next.rows.z≤0) && decide ((2:Int)^7∣next.rows.fv)) := by
  have hc := compileHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q h
  have hh := compileGrowingHistory_contract Q.slot.front.exitArena Q.historyArena Q.detectorArena record
    Q.detectorWork capacity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history hc.2.2.2.2.2
  have pred := compileHistory_selector F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history.record Q.detectorWork Q.history hh.2.2
    s next (Q.slot.front.exitBank.fv.wires.headD 0) F.counter.dropLast (Q.slot.front.exitBank.fv.wires.drop 7)
    hc.2.1 hc.2.2.2.2.1 values.counter (by rw [←List.cons_append,←hc.2.2.1]; exact rows.2.2.1) values.frozen (fun _ => inv.fveven)
  simpa only [hc.2.2.2.1] using pred

end ECDSAAdd.Arithmetic.Paper935
