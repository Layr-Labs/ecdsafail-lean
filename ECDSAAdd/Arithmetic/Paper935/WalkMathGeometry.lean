import ECDSAAdd.Arithmetic.Paper935.PostMathGeometry
import ECDSAAdd.Arithmetic.Paper935.WalkStaticBudget

namespace ECDSAAdd.Arithmetic.Paper935

/-- Static conditions consumed by arithmetic and post-stage semantics. -/
structure PublicSlot.StaticMathChecks (P : PublicSlot) (F : SlotRegisters) : Prop where
  front : P.front.MathChecks F (bankWidths P.front.exitBank)
  postOwned : (F.active::F.frozen::F.offset).toFinset⊆P.front.exitArena.live
  postRows : ∀ q∈P.front.exitBank.rows.flatMap WindowRow.wires,q≠F.active ∧ q≠F.frozen ∧ q∉F.offset
  postMeta : ∀ q∈[F.one,F.swap,F.parity]++F.counter,q≠F.active ∧ q≠F.frozen ∧ q∉F.offset
  offsetApart : F.active∉F.offset

/-- Every actual compiled slot inherits the address-only semantic conditions
from initial geometry and the same public budget recurrence. -/
theorem compileHistoricalWalk_mathChecks (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : compileHistoricalWalk F probeWidth A b record requests=some slots)
    (counterWidth : 2≤F.counter.length)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (budgets : historicalBudgets F probeWidth A.live.card (bankWidths b) record.length requests) :
    ∀ Q∈slots,Q.slot.StaticMathChecks F := by
  induction requests generalizing A b record slots with
  | nil => simp only [compileHistoricalWalk,Option.some.injEq] at compiled; subst slots; simp
  | cons r rs ih =>
    unfold compileHistoricalWalk at compiled
    obtain ⟨Q,hq,compiled⟩ := Option.bind_eq_some_iff.mp compiled
    obtain ⟨rest,hr,compiled⟩ := Option.bind_eq_some_iff.mp compiled
    cases compiled
    have head := budgets.1
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
    have tail := ih Q.historyArena Q.slot.front.exitBank Q.history.record rest hr grown.1 grown.2.1
      (by simpa only [hc,wc,len] using budgets.2)
    intro P hp
    rcases List.mem_cons.mp hp with hp|hp
    · subst P
      have publicCompiled := (compileHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ checked).1
      have frontCompiled := compilePublicSlot_front _ _ _ _ _ _ _ _ _
        (compileCheckedPublicSlot_contract _ _ _ _ _ _ _ _ _ publicCompiled).1
      have math := compileSlotFront_mathChecks A b (bankWidths b) (bankWidths b).addPad (historyWindow r.exitWidth)
        F record Q.slot.front frontCompiled widths distinct owned rfl rfl
        (by simp [RowWindow.addPad]) (by simp [RowWindow.addPad]) counterWidth
        (by simp [historyWindow]) head.padding head.resize head.counter
      have post := postMath_geometry Q.slot.front.exitArena F Q.slot.front.exitBank record exitDistinct exitOwned
      exact ⟨by simpa only [wc] using math,post.1,post.2.1,post.2.2.1,post.2.2.2⟩
    · exact tail P hp

end ECDSAAdd.Arithmetic.Paper935
