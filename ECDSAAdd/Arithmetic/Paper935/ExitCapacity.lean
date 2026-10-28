import ECDSAAdd.Arithmetic.Paper935.AuthorWalkRun

namespace ECDSAAdd.Arithmetic.Paper935

/-- Scalar recurrence for the actual persistent allocation, including history
growth. This is not a bound on ephemeral slot scratch. -/
def exitLiveCount : Nat → RowWindow → Nat → List HistoricalRequest → Nat
  | live,_,_,[] => live
  | live,b,n,r::rs => exitLiveCount
      ((live+(historyWindow r.exitWidth).payload-b.payload)+(r.capacity-n))
      (historyWindow r.exitWidth) (max r.capacity n) rs

theorem compileHistoricalWalk_exit_card (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : compileHistoricalWalk F probeWidth A b record requests=some slots)
    (counterNonempty : F.counter≠[])
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (budgets : historicalBudgets F probeWidth A.live.card (bankWidths b) record.length requests) :
    (walkExitArena A slots).live.card=exitLiveCount A.live.card (bankWidths b) record.length requests := by
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
    simpa only [walkExitArena,exitLiveCount,hc,wc,len] using tail

/-- Kernel evaluation of only the public scalar schedule. -/
theorem authorExitLiveCount : exitLiveCount 794 initialWindow 0 authorHistoricalRequests=907 := by
  decide +kernel

attribute [local irreducible] exitLiveCount compileHistoricalWalk historicalBudgets

theorem compileAuthorWalk_exit_card (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots) :
    (walkExitArena walkSeedArena slots).live.card=907 := by
  have h := compileHistoricalWalk_exit_card walkRegisters 6 walkSeedArena walkSeedBank []
    authorHistoricalRequests slots compiled (by decide) walkSeed_distinct walkSeed_owned
    (by simpa only [walkSeed_card,walkSeed_widths,List.length_nil] using authorHistoricalBudgets)
  simpa only [walkSeed_card,walkSeed_widths,List.length_nil,authorExitLiveCount] using h

theorem compileAuthorWalk_free_card (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots) :
    (arenaWires \ (walkExitArena walkSeedArena slots).live).card=28 := by
  rw [Finset.card_sdiff_of_subset (walkExitArena walkSeedArena slots).bounded,
    compileAuthorWalk_exit_card slots compiled]
  simp [arenaWires]

/-- Preserving the complete exit live set rules out a fresh 256-wire output
plus 17 distinct auxiliary wires. This does not rule out reversible reuse. -/
theorem compileAuthorWalk_no_fresh_output (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (fresh : Finset Wire) (inside : fresh⊆arenaWires)
    (separate : Disjoint fresh (walkExitArena walkSeedArena slots).live) : fresh.card≤28 := by
  have sub : fresh⊆arenaWires \ (walkExitArena walkSeedArena slots).live := by
    intro q h
    exact Finset.mem_sdiff.mpr ⟨inside h,fun bad => Finset.disjoint_left.mp separate h bad⟩
  have h := Finset.card_le_card sub
  rw [compileAuthorWalk_free_card slots compiled] at h
  exact h

end ECDSAAdd.Arithmetic.Paper935
