import ECDSAAdd.Arithmetic.Paper935.DecoderPinValues
import ECDSAAdd.Arithmetic.Paper935.HistoryUndoFromBranch
import ECDSAAdd.Arithmetic.Paper935.HistoricalSlotValueStep

namespace ECDSAAdd.Arithmetic.Paper935

theorem compileHistoricalSlot_history_undo (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (compiled : compileCheckedHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (D : SlotDecoder) (decoderCompiled : compileSlotDecoder F Q=some D)
    (distinct : (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.slot.front.exitArena.live)
    (budget : Q.historyArena.live.card+rowGrowth (Q.slot.front.exitBank.requests Q.slot.front.exitBank.decoderWidth)≤935)
    (offsetWidth : F.offset.length=6) (index : Nat) (indexBound : index<533)
    (p : Int) (old : PinState) (inv : ECDSAAdd.Divsteps.Inv p old.rows) (odd : p%2=1)
    (oldOffset : old.offset<decoderOffset index) (unset : old.frozen=false → old.offset=0)
    (frozenZero : old.frozen=true → old.rows.g=0)
    (firstZero : old.frozen=false → decide (498 ≤ index)=true →
      (ECDSAAdd.Divsteps.zStep old.rows).g=0 → old.rows.g≠0)
    (s : State) (values : F.OutputValues s.basis old (pinStep 498 index old))
    (rows : Q.slot.front.exitBank.Encodes s.basis (pinStep 498 index old).rows)
    (ready : Q.slot.front.exitArena.Ready s.basis)
    (fit : Q.history.selected s.basis=true →
      2*regValue record s.basis+(s.basis F.parity).toNat<2^(max capacity record.length))
    (m : List Bool) (ordinal cursor : Nat) :
    HistoryUndoAt Q.history (actualHistoryDecoder F p index Q) m ordinal cursor s := by
  have hc := (compileCheckedHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q compiled).1
  have slot := compileHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q hc
  have history := compileGrowingHistory_contract Q.slot.front.exitArena Q.historyArena Q.detectorArena record Q.detectorWork
    capacity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen F.counter
    (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history slot.2.2.2.2.2
  have ids := compileHistory_identity _ _ _ _ _ _ _ _ _ _ _ _ history.2.2
  have port : Q.history.port=F.parity := ids.2.2.2.2.2
  have inputGeom := historyValue_geometry Q.slot.front.exitArena F Q.slot.front.exitBank record distinct owned
  have grown := compileHistoricalSlot_exit_geometry A b record addWidth exitWidth F armed probeWidth offset capacity Q
    compiled distinct owned
  have growth := planHistoryGrow_correct Q.slot.front.exitArena Q.historyArena record Q.history.record capacity history.1
    inputGeom.1 inputGeom.2.1 s.basis ready
  have actualFit : Q.history.selected s.basis=true →
      2*regValue Q.history.record s.basis+(s.basis Q.history.port).toNat<2^Q.history.record.length := by
    simpa only [growth.1,growth.2.2.2.2.1,port] using fit
  have clean := compileGrowingHistory_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ slot.2.2.2.2.2
    inputGeom.1 inputGeom.2.1 s.basis ready values.one values.work0 values.work1 values.active
  have valid := (compileHistory_contract _ _ _ _ _ _ _ _ _ _ _ _ history.2.2).1
  apply historyUndoAt_of_branch_run Q.history valid s
    ⟨clean.2.1,clean.2.2.1,clean.2.2.2.1,clean.2.2.2.2.1,clean.2.2.2.2.2.1,clean.2.2.2.2.2.2⟩ actualFit
  let u := runWithTape Q.history.program m ordinal s
  have step := compileHistoricalSlot_value_step A b record addWidth exitWidth F armed probeWidth offset capacity Q
    compiled distinct owned old (pinStep 498 index old) s values rows ready fit m ordinal
  have pin := decoderPin_values index old unset
  have decoderRun := compileSlotDecoder_run F Q D decoderCompiled port grown.1 grown.2.1 budget offsetWidth index indexBound
    p old.rows inv odd old.frozen (decide (498 ≤ index)) old.offset oldOffset frozenZero firstZero
    u (m.drop cursor) step.2.1 step.1.one step.1.work0 step.1.work1 step.1.swap
    (by simpa only [pinStep_rows] using step.2.2.1)
    (by simpa only [pinStep_rows] using step.1.counter)
    (step.1.frozen.trans pin.1) (step.1.offset.trans pin.2)
  have selected := compileHistoricalSlot_selector A b record addWidth exitWidth F armed probeWidth offset capacity Q hc
    old (pinStep 498 index old) s.basis values rows p (pinStep_inv 498 index p old inv odd)
  have selection : Q.history.selected s.basis=
      (!(old.frozen || (!old.frozen && decide (498 ≤ index) && decide ((ECDSAAdd.Divsteps.zStep old.rows).g=0))) &&
        decide ((ECDSAAdd.Divsteps.zStep old.rows).z≤0) && decide ((2:Int)^7∣(ECDSAAdd.Divsteps.zStep old.rows).fv)) := by
    rw [selected,pin.1,pinStep_rows]
    cases old.frozen <;> simp
  have branch : s.basis Q.history.port=decide (ECDSAAdd.Divsteps.bbit old.rows=1) := by rw [port]; exact values.parity
  have zero : u.basis Q.history.port=false := by rw [port]; exact step.1.parity
  rw [actualHistoryDecoder_of_compiled F Q D decoderCompiled p index]
  simpa only [zero,Bool.false_xor,←selection,branch] using decoderRun

end ECDSAAdd.Arithmetic.Paper935
