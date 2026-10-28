import ECDSAAdd.Arithmetic.Paper935.SlotStaticHistoryUndo
import ECDSAAdd.Arithmetic.Paper935.WalkDecoderTotal
import ECDSAAdd.Arithmetic.Paper935.WalkUndoAssembly

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- Discharge every actual history recovery obligation along the connected
forward execution, using the compiled decoder and the original tape offsets. -/
theorem compileHistoricalWalk_history_undo (F : SlotRegisters) (probeWidth : Nat) (p x : Int)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : compileHistoricalWalk F probeWidth A b record requests=some slots)
    (counterWidth : F.counter.length=7) (offsetWidth : F.offset.length=6) (odd : p%2=1)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (budgets : historicalBudgets F probeWidth A.live.card (bankWidths b) record.length requests)
    (decoderBudget : decoderBudgets A.live.card (bankWidths b) record.length requests)
    (noEarly : ¬EarlyZero 498 p x)
    (index : Nat) (indexBound : index+requests.length≤533) (numerical : historicalNumericalInputs F 498 p x index (bankWidths b) record.length requests)
    (s : State) (m : List Bool) (ordinal cursor : Nat) (ready : A.Ready s.basis)
    (rows : b.Encodes s.basis (pinWalk 498 p x index).rows)
    (values : F.Values s.basis (pinWalk 498 p x index))
    (stack : regValue record s.basis=trajectoryHistory 498 7 p x index) :
    WalkHistoryUndo F (actualHistoryDecoder F p) m index ordinal cursor s slots := by
  induction requests generalizing A b record slots index s ordinal with
  | nil =>
    simp only [compileHistoricalWalk,Option.some.injEq] at compiled
    subst slots
    trivial
  | cons r rs ih =>
    have allChecks := compileHistoricalWalk_mathChecks F probeWidth A b record (r::rs) slots compiled (by omega)
      distinct owned budgets
    have original := compiled
    unfold compileHistoricalWalk at compiled
    obtain ⟨Q,hq,compiled⟩ := Option.bind_eq_some_iff.mp compiled
    obtain ⟨rest,hr,compiled⟩ := Option.bind_eq_some_iff.mp compiled
    cases compiled
    have head := budgets.1
    have num := numerical.1
    have widths : b.Widths (bankWidths b) := ⟨rfl,rfl,rfl,rfl⟩
    have nonempty : F.counter≠[] := by intro he; simp [he] at counterWidth
    obtain ⟨R,hR,exitWidths,exitDistinct,exitOwned,card⟩ :=
      compileHistoricalSlot_static_exists A b (bankWidths b) (bankWidths b).addPad (historyWindow r.exitWidth)
        F record r.armed probeWidth r.offset r.capacity widths distinct owned rfl rfl
        (by simp [RowWindow.addPad]) (by simp [RowWindow.addPad]) nonempty
        (by simp [historyWindow]) head.padding head.resize head.counter head.probePositive head.post head.offset
        (by simp [historyWindow]) head.history
    rw [hq,Option.some.injEq] at hR
    subst R
    have grown := compileHistoricalSlot_exit_geometry A b record (bankWidths b).addPad (historyWindow r.exitWidth)
      F r.armed probeWidth r.offset r.capacity Q hq exitDistinct exitOwned
    have wc : bankWidths Q.slot.front.exitBank=historyWindow r.exitWidth := by
      cases h : historyWindow r.exitWidth
      simp only [WindowBank.Widths,h] at exitWidths
      simp only [bankWidths,exitWidths.1,exitWidths.2.1,exitWidths.2.2.1,exitWidths.2.2.2]
    have checked := (compileCheckedHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ hq).1
    have len := (compileHistoricalSlot_lengths _ _ _ _ _ _ _ _ _ _ _ checked).1
    have hc : Q.historyArena.live.card=
        (A.live.card+(historyWindow r.exitWidth).payload-(bankWidths b).payload)+(r.capacity-record.length) := by
      rw [grown.2.2]
      omega
    have indexed : compileCheckedHistoricalSlot A b record (bankWidths b).addPad (historyWindow r.exitWidth) F
        (decide (498≤ index)) probeWidth (index+1-498) r.capacity=some Q := by
      rw [←num.armed,←num.offset]
      exact hq
    have offsets := pinWalk_offset_inputs 498 p x index
    have allDecoders := compileHistoricalWalk_decoders F probeWidth A b record (r::rs) (Q::rest)
      original counterWidth distinct owned budgets decoderBudget
    obtain ⟨D,hD⟩ := allDecoders Q (by simp)
    have padBudget : Q.historyArena.live.card+rowGrowth
        (Q.slot.front.exitBank.requests Q.slot.front.exitBank.decoderWidth)≤935 := by
      rw [decoder_rowGrowth,hc]
      have wf : Q.slot.front.exitBank.f.payload.length=(historyWindow r.exitWidth).f := exitWidths.1
      have wv : Q.slot.front.exitBank.fv.payload.length=(historyWindow r.exitWidth).fv := exitWidths.2.2.1
      rw [wf,wv]
      have bound := decoderBudget.1
      omega
    have decoderOffsetBound : (pinWalk 498 p x index).offset<decoderOffset index := by
      have bound := (pinWalk_record 498 p x index).2
      unfold decoderOffset
      omega
    have firstZero : (pinWalk 498 p x index).frozen=false → decide (498 ≤ index)=true →
        (zStep (pinWalk 498 p x index).rows).g=0 → (pinWalk 498 p x index).rows.g≠0 := by
      intro unfrozen _ _ zero
      have agree := (pinWalk_agrees 498 p x noEarly index).2
      have zg : (zWalk p x index).g=0 := by rw [←(pinWalk_agrees 498 p x noEarly index).1]; exact zero
      rw [unfrozen,zg] at agree
      simp at agree
    have history := compileHistoricalSlot_static_history_undo A b record (historyWindow r.exitWidth)
      F probeWidth index r.capacity Q indexed D hD padBudget offsetWidth (by simp only [List.length_cons] at indexBound; omega)
      (allChecks Q (by simp)) distinct owned exitDistinct exitOwned (pinWalk 498 p x index) s m ordinal
      ready rows num.inputRows values p (pinWalk_inv 498 p x odd index) odd (pinWalk_frozen_zero 498 p x index)
      num.exitRows num.counter offsets.1 offsets.2 decoderOffsetBound firstZero
      (cursor+recordedMeasurementCount (historicalWalkReverse F (actualHistoryDecoder F p) (index+1)
        (ordinal+recordedMeasurementCount (Q.program F)) rest))
      (by simpa only [trajectoryStore,pinWalk,stack] using num.push)
    have step := compileHistoricalSlot_static_run A b record (historyWindow r.exitWidth) F probeWidth 498 index r.capacity Q
      indexed (allChecks Q (by simp)) distinct owned exitDistinct exitOwned (pinWalk 498 p x index) s m ordinal
      ready rows num.inputRows values p (pinWalk_inv 498 p x odd index) odd (pinWalk_frozen_zero 498 p x index)
      num.exitRows num.counter offsets.1 offsets.2
      (by simpa only [trajectoryStore,pinWalk,stack] using num.push)
    let v := runWithTape (Q.program F) m ordinal s
    have nextStack : regValue Q.history.record v.basis=trajectoryHistory 498 7 p x (index+1) := by
      simpa only [trajectoryHistory,trajectoryStore,pinWalk,stack] using step.2.2.2
    have tail := ih Q.historyArena Q.slot.front.exitBank Q.history.record rest hr grown.1 grown.2.1
      (by simpa only [hc,wc,len] using budgets.2)
      (by simpa only [hc,wc,len] using decoderBudget.2) (index+1)
      (by simp only [List.length_cons] at indexBound; omega)
      (by simpa only [wc,len] using numerical.2) v
      (ordinal+recordedMeasurementCount (Q.program F)) step.2.1 step.2.2.1 step.1 nextStack
    exact ⟨history,tail⟩

end ECDSAAdd.Arithmetic.Paper935
