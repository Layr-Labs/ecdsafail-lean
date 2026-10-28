import ECDSAAdd.Arithmetic.Paper935.HistoricalWalkRun
import ECDSAAdd.Arithmetic.Paper935.PublicSlotStaticInverse
import ECDSAAdd.Arithmetic.Paper935.WalkRecovery

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- Arithmetic inverse obligations at every actual forward state. History
recovery is deliberately separate and will be composed at its own cursor. -/
def WalkArithmeticUndo (F : SlotRegisters) (m : List Bool) : Nat → State → List HistoricalSlot → Prop
  | _,_,[] => True
  | ordinal,s,Q::rest =>
      (∀ n,run (Q.slot.inverse F) n (run (Q.slot.program F) (m.drop ordinal) s)=s) ∧
      WalkArithmeticUndo F m (ordinal+recordedMeasurementCount (Q.program F))
        (runWithTape (Q.program F) m ordinal s) rest

/-- No per-step arithmetic inverse oracle is required: the forward invariant,
static geometry and the same mathematical fit bounds imply all round trips. -/
theorem compileHistoricalWalk_arithmetic_undo (F : SlotRegisters) (probeWidth tmin : Nat) (p x : Int)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : compileHistoricalWalk F probeWidth A b record requests=some slots)
    (counterWidth : 2≤F.counter.length) (odd : p%2=1)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (budgets : historicalBudgets F probeWidth A.live.card (bankWidths b) record.length requests)
    (index : Nat) (numerical : historicalNumericalInputs F tmin p x index (bankWidths b) record.length requests)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : A.Ready s.basis)
    (rows : b.Encodes s.basis (pinWalk tmin p x index).rows)
    (values : F.Values s.basis (pinWalk tmin p x index))
    (stack : regValue record s.basis=trajectoryHistory tmin 7 p x index) :
    WalkArithmeticUndo F m ordinal s slots := by
  induction requests generalizing A b record slots index s ordinal with
  | nil =>
    simp only [compileHistoricalWalk,Option.some.injEq] at compiled
    subst slots
    trivial
  | cons r rs ih =>
    have allChecks := compileHistoricalWalk_mathChecks F probeWidth A b record (r::rs) slots compiled counterWidth
      distinct owned budgets
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
        (decide (tmin≤ index)) probeWidth (index+1-tmin) r.capacity=some Q := by
      rw [←num.armed,←num.offset]
      exact hq
    have offsets := pinWalk_offset_inputs tmin p x index
    have publicCompiled := (compileHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _
      (compileCheckedHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ indexed).1).1
    have arithmetic (n : List Bool) := compileCheckedPublicSlot_static_roundtrip A b (historyWindow r.exitWidth)
      F record probeWidth tmin index Q.slot publicCompiled (allChecks Q (by simp)) distinct owned
      (pinWalk tmin p x index) s (m.drop ordinal) n ready rows num.inputRows values p
      (pinWalk_inv tmin p x odd index) odd (pinWalk_inv tmin p x odd index).fodd
      (pinWalk_frozen_zero tmin p x index)
      (by simpa only [pinWalk,pinStep_rows] using num.exitRows)
      (by simpa only [pinWalk,pinStep_rows] using num.counter) offsets.1 offsets.2
    have step := compileHistoricalSlot_static_run A b record (historyWindow r.exitWidth) F probeWidth tmin index r.capacity Q
      indexed (allChecks Q (by simp)) distinct owned exitDistinct exitOwned (pinWalk tmin p x index) s m ordinal
      ready rows num.inputRows values p (pinWalk_inv tmin p x odd index) odd (pinWalk_frozen_zero tmin p x index)
      num.exitRows num.counter offsets.1 offsets.2
      (by simpa only [trajectoryStore,pinWalk,stack] using num.push)
    let v := runWithTape (Q.program F) m ordinal s
    have nextStack : regValue Q.history.record v.basis=trajectoryHistory tmin 7 p x (index+1) := by
      simpa only [trajectoryHistory,trajectoryStore,pinWalk,stack] using step.2.2.2
    have tail := ih Q.historyArena Q.slot.front.exitBank Q.history.record rest hr grown.1 grown.2.1
      (by simpa only [hc,wc,len] using budgets.2) (index+1)
      (by simpa only [wc,len] using numerical.2) v
      (ordinal+recordedMeasurementCount (Q.program F)) step.2.1 step.2.2.1 step.1 nextStack
    exact ⟨arithmetic,tail⟩

end ECDSAAdd.Arithmetic.Paper935
