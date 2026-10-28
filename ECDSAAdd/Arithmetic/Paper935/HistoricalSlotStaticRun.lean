import ECDSAAdd.Arithmetic.Paper935.HistoricalSlotValueStep

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- Complete actual recorded slot: mathematical rows/metadata and the stack
integer advance together. The push bound is on the mathematical selector and
incoming stack, rather than an intermediate interpreter state. -/
theorem compileHistoricalSlot_static_run (A : Arena) (b : WindowBank) (record : List Wire)
    (exitWidth : RowWindow) (F : SlotRegisters) (probeWidth tmin index capacity : Nat) (Q : HistoricalSlot)
    (compiled : compileCheckedHistoricalSlot A b record (bankWidths b).addPad exitWidth F
      (decide (tmin≤ index)) probeWidth (index+1-tmin) capacity=some Q)
    (checks : Q.slot.StaticMathChecks F)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (exitDistinct : (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (exitOwned : (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.slot.front.exitArena.live)
    (old : PinState) (s : State) (m : List Bool) (ordinal : Nat) (ready : A.Ready s.basis)
    (rows : b.Encodes s.basis old.rows) (fit : (bankWidths b).Fits old.rows)
    (values : F.Values s.basis old) (p : Int) (inv : Inv p old.rows) (odd : p%2=1)
    (frozenZero : old.frozen=true → old.rows.g=0)
    (exitfit : exitWidth.Fits (pinStep tmin index old).rows)
    (zfit : PayloadFits (F.counter.length-1) (pinStep tmin index old).rows.z)
    (oldOffset : tmin≤ index → old.offset< index+1-tmin) (activeOffset : old.frozen=false → old.offset=0)
    (pushFit : (!(pinStep tmin index old).frozen && decide ((pinStep tmin index old).rows.z≤0) &&
        decide ((2:Int)^7∣(pinStep tmin index old).rows.fv))=true →
      2*regValue record s.basis+(parityControl old.rows).toNat<2^(max capacity record.length)) :
    let next := pinStep tmin index old
    let t := runWithTape (Q.program F) m ordinal s
    F.Values t.basis next ∧ Q.historyArena.Ready t.basis ∧ Q.slot.front.exitBank.Encodes t.basis next.rows ∧
    regValue Q.history.record t.basis=(if !next.frozen && decide (next.rows.z≤0) && decide ((2:Int)^7∣next.rows.fv) then
      2*regValue record s.basis+(parityControl old.rows).toNat else regValue record s.basis) := by
  have hc := (compileCheckedHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ compiled).1
  have publicCompiled := (compileHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ hc).1
  let v := run (Q.slot.program F) (m.drop ordinal) s
  have publicRun := compileCheckedPublicSlot_static_run A b exitWidth F record probeWidth tmin index Q.slot publicCompiled
    checks distinct owned old s (m.drop ordinal) ready rows fit values p inv odd inv.fodd frozenZero
    (by simpa only [pinStep_rows] using exitfit) (by simpa only [pinStep_rows] using zfit) oldOffset activeOffset
  have nonempty : F.counter≠[] := by
    intro he
    have h := checks.front.counterWidth
    simp [he] at h
  have coefficientNonempty : Q.slot.front.exitBank.fv.payload≠[] := by
    intro he
    have h := checks.front.coefficientWidth
    simp only [bankWidths,he,List.length_nil] at h
    omega
  have stackValue : regValue record v.basis=regValue record s.basis :=
    compilePublicSlot_history_value A b (bankWidths b).addPad exitWidth F (decide (tmin≤ index)) probeWidth
      (index+1-tmin) Q.slot record (compileCheckedPublicSlot_contract _ _ _ _ _ _ _ _ _ publicCompiled).1
      nonempty coefficientNonempty distinct owned s (m.drop ordinal)
  have selector := compileHistoricalSlot_selector A b record (bankWidths b).addPad exitWidth F (decide (tmin≤ index))
    probeWidth (index+1-tmin) capacity Q hc old (pinStep tmin index old) v.basis publicRun.2.2.2 publicRun.2.2.1
    p (pinStep_inv tmin index p old inv odd)
  have branch : v.basis F.parity=parityControl old.rows := by
    rw [publicRun.2.2.2.parity]
    unfold bbit parityControl
    split_ifs with swap
    · rw [inv.fodd,swap.2]
    · rfl
  have actualFit : Q.history.selected v.basis=true →
      2*regValue record v.basis+(v.basis F.parity).toNat<2^(max capacity record.length) := by
    simpa only [selector,stackValue,branch] using pushFit
  have historyRun := compileHistoricalSlot_value_step A b record (bankWidths b).addPad exitWidth F (decide (tmin≤ index))
    probeWidth (index+1-tmin) capacity Q compiled exitDistinct exitOwned old (pinStep tmin index old) v
    publicRun.2.2.2 publicRun.2.2.1 publicRun.2.1 actualFit m
    (ordinal+recordedMeasurementCount (embedRecorded (Q.slot.program F)))
  dsimp only
  rw [HistoricalSlot.program,runWithTape_append,runWithTape_embedRecorded]
  exact ⟨historyRun.1,historyRun.2.1,historyRun.2.2.1,by
    simpa only [selector,stackValue,branch] using historyRun.2.2.2⟩

end ECDSAAdd.Arithmetic.Paper935
