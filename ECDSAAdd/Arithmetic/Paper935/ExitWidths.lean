import ECDSAAdd.Arithmetic.Paper935.AuthorWalkRun

namespace ECDSAAdd.Arithmetic.Paper935

def exitWindow : RowWindow → List HistoricalRequest → RowWindow
  | w,[] => w
  | _,r::rs => exitWindow (historyWindow r.exitWidth) rs

theorem compileHistoricalWalk_exit_widths (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : compileHistoricalWalk F probeWidth A b record requests=some slots)
    (counterNonempty : F.counter≠[])
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (budgets : historicalBudgets F probeWidth A.live.card (bankWidths b) record.length requests) :
    bankWidths (walkExitBank b slots)=exitWindow (bankWidths b) requests := by
  induction requests generalizing A b record slots with
  | nil =>
    simp only [compileHistoricalWalk,Option.some.injEq] at compiled
    subst slots
    rfl
  | cons r rs ih =>
    have head := budgets.1
    have widths : b.Widths (bankWidths b) := ⟨rfl,rfl,rfl,rfl⟩
    obtain ⟨Q,hq,exitWidths,exitDistinct,exitOwned,card⟩ :=
      compileHistoricalSlot_static_exists A b (bankWidths b) (bankWidths b).addPad (historyWindow r.exitWidth)
        F record r.armed probeWidth r.offset r.capacity widths distinct owned rfl rfl
        (by simp [RowWindow.addPad]) (by simp [RowWindow.addPad]) counterNonempty
        (by simp [historyWindow]) head.padding head.resize head.counter head.probePositive head.post head.offset
        (by simp [historyWindow]) head.history
    have grown := compileHistoricalSlot_exit_geometry A b record (bankWidths b).addPad (historyWindow r.exitWidth)
      F r.armed probeWidth r.offset r.capacity Q hq exitDistinct exitOwned
    have wc : bankWidths Q.slot.front.exitBank=historyWindow r.exitWidth := by
      cases h : historyWindow r.exitWidth
      simp only [WindowBank.Widths,h] at exitWidths
      simp only [bankWidths,exitWidths.1,exitWidths.2.1,exitWidths.2.2.1,exitWidths.2.2.2]
    have len := (compileHistoricalSlot_lengths A b record (bankWidths b).addPad (historyWindow r.exitWidth)
      F r.armed probeWidth r.offset r.capacity Q
      (compileCheckedHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ hq).1).1
    have hc : Q.historyArena.live.card=
        (A.live.card+(historyWindow r.exitWidth).payload-(bankWidths b).payload)+(r.capacity-record.length) := by
      rw [grown.2.2]
      omega
    unfold compileHistoricalWalk at compiled
    obtain ⟨Q',hq',compiled⟩ := Option.bind_eq_some_iff.mp compiled
    have eq : Q'=Q := Option.some.inj (hq'.symm.trans hq)
    subst Q'
    obtain ⟨rest,hr,h⟩ := Option.bind_eq_some_iff.mp compiled
    cases h
    have tail := ih Q.historyArena Q.slot.front.exitBank Q.history.record rest hr grown.1 grown.2.1
      (by simpa only [hc,wc,len] using budgets.2)
    simpa only [walkExitBank,exitWindow,wc] using tail


theorem authorExitWindow : exitWindow initialWindow authorHistoricalRequests=⟨3,4,280,280⟩ := by
  decide +kernel

attribute [local irreducible] exitWindow compileHistoricalWalk historicalBudgets

theorem compileAuthorWalk_exit_widths (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots) :
    (walkExitBank walkSeedBank slots).Widths ⟨3,4,280,280⟩ := by
  have h := compileHistoricalWalk_exit_widths walkRegisters 6 walkSeedArena walkSeedBank []
    authorHistoricalRequests slots compiled (by decide) walkSeed_distinct walkSeed_owned
    (by simpa only [walkSeed_card,walkSeed_widths,List.length_nil] using authorHistoricalBudgets)
  rw [walkSeed_widths,authorExitWindow] at h
  have f := congrArg RowWindow.f h
  have g := congrArg RowWindow.g h
  have fv := congrArg RowWindow.fv h
  have gv := congrArg RowWindow.gv h
  exact ⟨f,g,fv,gv⟩

end ECDSAAdd.Arithmetic.Paper935
