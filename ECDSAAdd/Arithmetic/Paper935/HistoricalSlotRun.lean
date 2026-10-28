import ECDSAAdd.Arithmetic.Paper935.HistoricalSlotCompiler

namespace ECDSAAdd.Arithmetic.Paper935

theorem SlotRegisters.values_after_history (F : SlotRegisters) (s t : BasisState) (old next : PinState)
    (values : F.OutputValues s old next) (parity : t F.parity=false)
    (keep : ∀ q∈[F.one,F.frozen,F.active,F.swap,F.work0,F.work1]++F.counter++F.offset,t q=s q) :
    F.Values t next := by
  constructor
  · rw [keep F.one (by simp)]; exact values.one
  · rw [keep F.frozen (by simp)]; exact values.frozen
  · exact parity
  · rw [keep F.active (by simp)]; exact values.active
  · rw [keep F.swap (by simp)]; exact values.swap
  · rw [keep F.work0 (by simp)]; exact values.work0
  · rw [keep F.work1 (by simp)]; exact values.work1
  · unfold signedRegValue
    rw [regValue_congr F.counter t s (by intro q hq; exact keep q (by simp [hq]))]
    exact values.counter
  · rw [regValue_congr F.offset t s (by intro q hq; exact keep q (by simp [hq]))]
    exact values.offset

/-- The emitted history stage clears the retained parity bit, restores the
metadata input format for the next slot, and returns the detector pool. -/
theorem compileHistoricalSlot_history_run (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (old next : PinState) (s : State) (values : F.OutputValues s.basis old next)
    (ready : Q.slot.front.exitArena.Ready s.basis) (hn : record.Nodup)
    (owned : record.toFinset⊆Q.slot.front.exitArena.live) (portOwned : F.parity∈Q.historyArena.live)
    (apart : ∀ q∈[F.one,F.frozen,F.active,F.swap,F.work0,F.work1]++F.counter++F.offset,
      q∉Q.history.port::Q.history.record)
    (fit : Q.history.selected s.basis=true →
      2*regValue Q.history.record s.basis+(s.basis Q.history.port).toNat<2^Q.history.record.length)
    (m : List Bool) (ordinal : Nat) :
    let t := runWithTape Q.history.program m ordinal s
    F.Values t.basis next ∧ Q.historyArena.Ready t.basis ∧
    Q.detectorArena.release Q.detectorWork.toFinset t.basis=some Q.historyArena ∧
    regValue Q.history.record t.basis=(if Q.history.selected s.basis then
      2*regValue record s.basis+(s.basis F.parity).toNat else regValue record s.basis) ∧
    (∀ q,q∉Q.history.port::Q.history.record → t.basis q=s.basis q) := by
  have hc := compileHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q h
  have hh := compileGrowingHistory_contract Q.slot.front.exitArena Q.historyArena Q.detectorArena record
    Q.detectorWork capacity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history hc.2.2.2.2.2
  have ids := compileHistory_identity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history.record Q.detectorWork Q.history hh.2.2
  have spec := compileGrowingHistory_spec Q.slot.front.exitArena Q.historyArena Q.detectorArena record
    Q.detectorWork capacity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history hc.2.2.2.2.2
    hn owned s ready values.one values.work0 values.work1 values.active fit m ordinal
  have release := compileGrowingHistory_release Q.slot.front.exitArena Q.historyArena Q.detectorArena record
    Q.detectorWork capacity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen
    F.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history hc.2.2.2.2.2
    hn owned portOwned s ready values.one values.work0 values.work1 values.active fit m ordinal
  refine ⟨F.values_after_history s.basis _ old next values ?_ (fun q hq => spec.2.2 q (apart q hq)),release.2,release.1,?_,spec.2.2⟩
  · simpa only [ids.2.2.2.2.2] using spec.1
  · simpa only [ids.2.2.2.2.2] using spec.2.1

end ECDSAAdd.Arithmetic.Paper935
