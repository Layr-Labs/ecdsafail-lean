import ECDSAAdd.Arithmetic.Paper935.ExitCapacity
import ECDSAAdd.Arithmetic.Paper935.WalkWidthStaticBudget

namespace ECDSAAdd.Arithmetic.Paper935

/-- Scalar recurrence for the actual persistent allocation, including history
growth. This is not a bound on ephemeral slot scratch. -/
def exitLiveCountWidth (hw : Nat) : Nat → RowWindow → Nat → List HistoricalRequest → Nat
  | live,_,_,[] => live
  | live,b,n,r::rs => exitLiveCountWidth hw
      ((live+(historyWindowWidth hw r.exitWidth).payload-b.payload)+(r.capacity-n))
      (historyWindowWidth hw r.exitWidth) (max r.capacity n) rs

theorem compileHistoricalWalkWidth_exit_card (hw : Nat) (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : compileHistoricalWalkWidth hw F probeWidth A b record requests=some slots)
    (counterNonempty : F.counter≠[])
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (budgets : historicalBudgetsWidth hw F probeWidth A.live.card (bankWidths b) record.length requests) :
    (walkExitArena A slots).live.card=exitLiveCountWidth hw A.live.card (bankWidths b) record.length requests := by
  induction requests generalizing A b record slots with
  | nil =>
    simp only [compileHistoricalWalkWidth,Option.some.injEq] at compiled
    subst slots
    rfl
  | cons r rs ih =>
    have head := budgets.1
    have widths : b.Widths (bankWidths b) := ⟨rfl,rfl,rfl,rfl⟩
    obtain ⟨Q,hq,exitWidths,exitDistinct,exitOwned,card⟩ :=
      compileHistoricalSlotWidth_static_exists hw A b (bankWidths b) (bankWidths b).addPad (historyWindowWidth hw r.exitWidth)
        F record r.armed probeWidth r.offset r.capacity widths distinct owned rfl rfl
        (by simp [RowWindow.addPad]) (by simp [RowWindow.addPad]) counterNonempty
        (by simp [historyWindowWidth]) head.padding head.resize head.counter head.probePositive head.post head.offset
        (by simp [historyWindowWidth]) head.history
    have grown := compileHistoricalSlotWidth_exit_geometry hw A b record (bankWidths b).addPad (historyWindowWidth hw r.exitWidth)
      F r.armed probeWidth r.offset r.capacity Q hq exitDistinct exitOwned
    have wc : bankWidths Q.slot.front.exitBank=historyWindowWidth hw r.exitWidth := by
      cases h : historyWindowWidth hw r.exitWidth
      simp only [WindowBank.Widths,h] at exitWidths
      simp only [bankWidths,exitWidths.1,exitWidths.2.1,exitWidths.2.2.1,exitWidths.2.2.2]
    have len := (compileHistoricalSlotWidth_lengths hw A b record (bankWidths b).addPad (historyWindowWidth hw r.exitWidth)
      F r.armed probeWidth r.offset r.capacity Q
      (compileCheckedHistoricalSlotWidth_contract hw _ _ _ _ _ _ _ _ _ _ _ hq).1).1
    have hc : Q.historyArena.live.card=
        (A.live.card+(historyWindowWidth hw r.exitWidth).payload-(bankWidths b).payload)+(r.capacity-record.length) := by
      rw [grown.2.2]
      omega
    unfold compileHistoricalWalkWidth at compiled
    obtain ⟨Q',hq',compiled⟩ := Option.bind_eq_some_iff.mp compiled
    have eq : Q'=Q := Option.some.inj (hq'.symm.trans hq)
    subst Q'
    obtain ⟨rest,hr,h⟩ := Option.bind_eq_some_iff.mp compiled
    cases h
    have tail := ih Q.historyArena Q.slot.front.exitBank Q.history.record rest hr grown.1 grown.2.1
      (by simpa only [hc,wc,len] using budgets.2)
    simpa only [walkExitArena,exitLiveCountWidth,hc,wc,len] using tail


end ECDSAAdd.Arithmetic.Paper935
