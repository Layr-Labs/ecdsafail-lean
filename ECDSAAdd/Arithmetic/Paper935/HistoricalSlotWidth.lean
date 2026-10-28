import ECDSAAdd.Arithmetic.Paper935.HistoricalSlotCompiler

namespace ECDSAAdd.Arithmetic.Paper935

/-- Append the actual growing history stage to the public arithmetic slot.
The coefficient view is parameterized; the old six-bit instance remains unchanged. -/
def compileHistoricalSlotWidth (historyWidth : Nat) (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) : Option HistoricalSlot := do
  let P ← compileCheckedPublicSlot A b addWidth exitWidth F armed probeWidth offset
  let vs := P.front.exitBank.fv.wires
  if F.counter=F.counter.dropLast++[F.counter.getLastD 0] ∧
      vs=vs.headD 0::(vs.drop 1 |>.take historyWidth)++vs.drop (historyWidth+1) ∧
      (vs.drop 1 |>.take historyWidth).length=historyWidth ∧ vs.drop (historyWidth+1)≠[] then
    let (B,D,work,H) ← compileGrowingHistory P.front.exitArena record capacity
      F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
      F.counter (vs.drop 1 |>.take historyWidth)
    pure ⟨P,B,D,work,H⟩
  else none

theorem compileHistoricalSlotWidth_contract (historyWidth : Nat) (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileHistoricalSlotWidth historyWidth A b record addWidth exitWidth F armed probeWidth offset capacity=some Q) :
    compileCheckedPublicSlot A b addWidth exitWidth F armed probeWidth offset=some Q.slot ∧
    F.counter=F.counter.dropLast++[F.counter.getLastD 0] ∧
    Q.slot.front.exitBank.fv.wires=Q.slot.front.exitBank.fv.wires.headD 0::
      (Q.slot.front.exitBank.fv.wires.drop 1 |>.take historyWidth)++Q.slot.front.exitBank.fv.wires.drop (historyWidth+1) ∧
    (Q.slot.front.exitBank.fv.wires.drop 1 |>.take historyWidth).length=historyWidth ∧
    Q.slot.front.exitBank.fv.wires.drop (historyWidth+1)≠[] ∧
    compileGrowingHistory Q.slot.front.exitArena record capacity F.one F.work0 F.work1
      (F.counter.getLastD 0) F.active F.parity F.frozen F.counter
      (Q.slot.front.exitBank.fv.wires.drop 1 |>.take historyWidth)=
        some (Q.historyArena,Q.detectorArena,Q.detectorWork,Q.history) := by
  unfold compileHistoricalSlotWidth at h
  obtain ⟨P,hp,h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  next views =>
    obtain ⟨⟨B,D,work,H⟩,hh,h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact ⟨hp,views.1,views.2.1,views.2.2.1,views.2.2.2,hh⟩
  next invalid => simp at h

theorem compileHistoricalSlotWidth_depth_capacity (historyWidth : Nat) (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileHistoricalSlotWidth historyWidth A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (s : BasisState) (ready : Q.slot.front.exitArena.Ready s)
    (hn : record.Nodup) (owned : record.toFinset⊆Q.slot.front.exitArena.live) :
    Q.history.low.length+1=historyWidth+1 ∧ Q.history.record.length=max capacity record.length := by
  have hc := compileHistoricalSlotWidth_contract historyWidth A b record addWidth exitWidth F armed probeWidth offset capacity Q h
  have grow := compileGrowingHistory_capacity Q.slot.front.exitArena Q.historyArena Q.detectorArena record
    Q.detectorWork capacity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take historyWidth) Q.history hc.2.2.2.2.2 hn owned s ready
  exact ⟨by rw [grow.2.1,hc.2.2.2.1],grow.1⟩

/-- Bind the compiled store selector to the same post-slot state produced by
compileCheckedPublicSlot_run, with no guessed coefficient/register mapping. -/
theorem compileHistoricalSlotWidth_selector (historyWidth : Nat) (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileHistoricalSlotWidth historyWidth A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (old next : PinState) (s : BasisState) (values : F.OutputValues s old next)
    (rows : Q.slot.front.exitBank.Encodes s next.rows)
    (p : Int) (inv : ECDSAAdd.Divsteps.Inv p next.rows) :
    Q.history.selected s=(!next.frozen && decide (next.rows.z≤0) && decide ((2:Int)^(historyWidth+1)∣next.rows.fv)) := by
  have hc := compileHistoricalSlotWidth_contract historyWidth A b record addWidth exitWidth F armed probeWidth offset capacity Q h
  have hh := compileGrowingHistory_contract Q.slot.front.exitArena Q.historyArena Q.detectorArena record
    Q.detectorWork capacity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take historyWidth) Q.history hc.2.2.2.2.2
  have pred := compileHistory_selector F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take historyWidth) Q.history.record Q.detectorWork Q.history hh.2.2
    s next (Q.slot.front.exitBank.fv.wires.headD 0) F.counter.dropLast (Q.slot.front.exitBank.fv.wires.drop (historyWidth+1))
    hc.2.1 hc.2.2.2.2.1 values.counter (by rw [←List.cons_append,←hc.2.2.1]; exact rows.2.2.1) values.frozen (fun _ => inv.fveven)
  simpa only [hc.2.2.2.1] using pred

/-- The existing mixed instance is definitionally preserved. -/
theorem compileHistoricalSlotWidth_six (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) :
    compileHistoricalSlotWidth 6 A b record addWidth exitWidth F armed probeWidth offset capacity=
      compileHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity := rfl

end ECDSAAdd.Arithmetic.Paper935
