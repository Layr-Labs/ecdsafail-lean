import ECDSAAdd.Arithmetic.Paper935.SlotHistoryUndo

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- History recovery at the actual post-arithmetic state follows from the
compiled layout and numerical bounds, including preservation of the stack. -/
theorem compileHistoricalSlot_static_history_undo (A : Arena) (b : WindowBank) (record : List Wire)
    (exitWidth : RowWindow) (F : SlotRegisters) (probeWidth index capacity : Nat) (Q : HistoricalSlot)
    (compiled : compileCheckedHistoricalSlot A b record (bankWidths b).addPad exitWidth F
      (decide (498≤ index)) probeWidth (index+1-498) capacity=some Q)
    (D : SlotDecoder) (decoderCompiled : compileSlotDecoder F Q=some D)
    (budget : Q.historyArena.live.card+rowGrowth (Q.slot.front.exitBank.requests Q.slot.front.exitBank.decoderWidth)≤935)
    (offsetWidth : F.offset.length=6) (indexBound : index<533)
    (checks : Q.slot.StaticMathChecks F)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (exitDistinct : (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (exitOwned : (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.slot.front.exitArena.live)
    (old : PinState) (s : State) (m : List Bool) (ordinal : Nat) (ready : A.Ready s.basis)
    (rows : b.Encodes s.basis old.rows) (fit : (bankWidths b).Fits old.rows)
    (values : F.Values s.basis old) (p : Int) (inv : Inv p old.rows) (odd : p%2=1)
    (frozenZero : old.frozen=true → old.rows.g=0)
    (exitfit : exitWidth.Fits (pinStep 498 index old).rows)
    (zfit : PayloadFits (F.counter.length-1) (pinStep 498 index old).rows.z)
    (oldOffset : 498≤ index → old.offset< index+1-498) (activeOffset : old.frozen=false → old.offset=0)
    (decoderOldOffset : old.offset<decoderOffset index)
    (firstZero : old.frozen=false → decide (498 ≤ index)=true → (zStep old.rows).g=0 → old.rows.g≠0)
    (cursor : Nat)
    (pushFit : (!(pinStep 498 index old).frozen && decide ((pinStep 498 index old).rows.z≤0) &&
        decide ((2:Int)^7∣(pinStep 498 index old).rows.fv))=true →
      2*regValue record s.basis+(parityControl old.rows).toNat<2^(max capacity record.length)) :
    HistoryUndoAt Q.history (actualHistoryDecoder F p index Q) m
      (ordinal+measurementCount (Q.slot.program F)) cursor (run (Q.slot.program F) (m.drop ordinal) s) := by
  have hc := (compileCheckedHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ compiled).1
  have publicCompiled := (compileHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ hc).1
  let v := run (Q.slot.program F) (m.drop ordinal) s
  have publicRun := compileCheckedPublicSlot_static_run A b exitWidth F record probeWidth 498 index Q.slot publicCompiled
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
    compilePublicSlot_history_value A b (bankWidths b).addPad exitWidth F (decide (498≤ index)) probeWidth
      (index+1-498) Q.slot record (compileCheckedPublicSlot_contract _ _ _ _ _ _ _ _ _ publicCompiled).1
      nonempty coefficientNonempty distinct owned s (m.drop ordinal)
  have selector := compileHistoricalSlot_selector A b record (bankWidths b).addPad exitWidth F (decide (498≤ index))
    probeWidth (index+1-498) capacity Q hc old (pinStep 498 index old) v.basis publicRun.2.2.2 publicRun.2.2.1
    p (pinStep_inv 498 index p old inv odd)
  have branch : v.basis F.parity=parityControl old.rows := by
    rw [publicRun.2.2.2.parity]
    unfold bbit parityControl
    split_ifs with swap
    · rw [inv.fodd,swap.2]
    · rfl
  have actualFit : Q.history.selected v.basis=true →
      2*regValue record v.basis+(v.basis F.parity).toNat<2^(max capacity record.length) := by
    simpa only [selector,stackValue,branch] using pushFit
  exact compileHistoricalSlot_history_undo A b record (bankWidths b).addPad exitWidth F (decide (498≤ index))
    probeWidth (index+1-498) capacity Q compiled D decoderCompiled exitDistinct exitOwned budget offsetWidth
    index indexBound p old inv odd decoderOldOffset activeOffset frozenZero firstZero v publicRun.2.2.2
    publicRun.2.2.1 publicRun.2.1 actualFit m (ordinal+measurementCount (Q.slot.program F)) cursor

end ECDSAAdd.Arithmetic.Paper935
