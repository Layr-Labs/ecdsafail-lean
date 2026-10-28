import ECDSAAdd.Arithmetic.Paper935.ExitWidths
import ECDSAAdd.Arithmetic.Paper935.HmrWalkStaticTotal

namespace ECDSAAdd.Arithmetic.Paper935

def exitWindowWidth (hw : Nat) : RowWindow → List HistoricalRequest → RowWindow
  | w,[] => w
  | _,r::rs => exitWindowWidth hw (historyWindowWidth hw r.exitWidth) rs

theorem compileHistoricalWalkWidth_exit_widths (hw : Nat) (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : compileHistoricalWalkWidth hw F probeWidth A b record requests=some slots)
    (counterNonempty : F.counter≠[])
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (budgets : historicalBudgetsWidth hw F probeWidth A.live.card (bankWidths b) record.length requests) :
    bankWidths (walkExitBank b slots)=exitWindowWidth hw (bankWidths b) requests := by
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
    simpa only [walkExitBank,exitWindowWidth,wc] using tail


theorem hmrExitWindow : exitWindowWidth 4 initialWindow authorHistoricalRequests=⟨3,4,280,280⟩ := by
  decide +kernel

attribute [local irreducible] exitWindowWidth compileHistoricalWalkWidth historicalBudgetsWidth

theorem compileHmrWalk_exit_widths (slots : List HistoricalSlot) (compiled : compileHmrWalk=some slots) :
    (walkExitBank walkSeedBank slots).Widths ⟨3,4,280,280⟩ := by
  have h := compileHistoricalWalkWidth_exit_widths 4 hmrWalkRegisters 6 hmrWalkSeedArena walkSeedBank []
    authorHistoricalRequests slots compiled (by decide) hmrWalkSeed_distinct hmrWalkSeed_owned
    (by simpa only [hmrWalkSeed_card,hmrWalkSeed_widths,List.length_nil] using hmrHistoricalBudgets)
  rw [hmrWalkSeed_widths,hmrExitWindow] at h
  have f := congrArg RowWindow.f h
  have g := congrArg RowWindow.g h
  have fv := congrArg RowWindow.fv h
  have gv := congrArg RowWindow.gv h
  exact ⟨f,g,fv,gv⟩

end ECDSAAdd.Arithmetic.Paper935
