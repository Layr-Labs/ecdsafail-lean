import ECDSAAdd.Arithmetic.Paper935.OutputCapacity

namespace ECDSAAdd.Arithmetic.Paper935

/-- Scalar counter allocation trace of the actual public schedule. -/
def counterLiveCounts (counterWidth : Nat) : Nat → RowWindow → Nat → List HistoricalRequest → List Nat
  | _,_,_,[] => []
  | live,b,n,r::rs =>
      (live+(historyWindow r.exitWidth).payload-b.payload+(2*counterWidth-1)) ::
      counterLiveCounts counterWidth
        ((live+(historyWindow r.exitWidth).payload-b.payload)+(r.capacity-n))
        (historyWindow r.exitWidth) (max r.capacity n) rs

theorem planCounterScratch_card (A B : Arena) (width : Nat) (zero carry : List Wire)
    (h : planCounterScratch A width=some (B,zero,carry)) :
    B.live.card=A.live.card+(2*width-1) := by
  unfold planCounterScratch at h
  obtain ⟨⟨C,qs⟩,borrow,h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact (A.borrowMany_live B (2*width-1) qs borrow).2

theorem compileHistoricalWalk_counter_cards (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : compileHistoricalWalk F probeWidth A b record requests=some slots)
    (counterNonempty : F.counter≠[])
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (budgets : historicalBudgets F probeWidth A.live.card (bankWidths b) record.length requests) :
    (slots.map fun Q => Q.slot.front.counterArena.live.card)=counterLiveCounts F.counter.length A.live.card (bankWidths b) record.length requests := by
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
    have raw := (compileCheckedHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ hq).1
    have publicCompiled := (compileHistoricalSlot_contract _ _ _ _ _ _ _ _ _ _ _ raw).1
    have publicRaw := (compileCheckedPublicSlot_contract _ _ _ _ _ _ _ _ _ publicCompiled).1
    have front := compilePublicSlot_front _ _ _ _ _ _ _ _ _ publicRaw
    have counter := (compileSlotFront_contract _ _ _ _ _ _ front).counter
    have counterCard := planCounterScratch_card _ _ _ _ _ counter
    have exitCard : Q.slot.front.exitArena.live.card=A.live.card+(historyWindow r.exitWidth).payload-(bankWidths b).payload := by omega
    have tail := ih Q.historyArena Q.slot.front.exitBank Q.history.record rest hr grown.1 grown.2.1
      (by simpa only [hc,wc,len] using budgets.2)
    simp only [List.map_cons,counterLiveCounts]
    rw [counterCard,exitCard]
    congr 1
    simpa only [hc,wc,len] using tail

/-- Only scalar schedule data are evaluated by the kernel. -/
theorem authorCounterFull : 935∈counterLiveCounts 7 794 initialWindow 0 authorHistoricalRequests := by
  decide +kernel

attribute [local irreducible] counterLiveCounts compileHistoricalWalk historicalBudgets

theorem compileAuthorWalk_counter_full (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots) :
    ∃ Q∈slots,Q.slot.front.counterArena.live=arenaWires := by
  have cards := compileHistoricalWalk_counter_cards walkRegisters 6 walkSeedArena walkSeedBank []
    authorHistoricalRequests slots compiled (by decide) walkSeed_distinct walkSeed_owned
    (by simpa only [walkSeed_card,walkSeed_widths,List.length_nil] using authorHistoricalBudgets)
  have member : 935∈slots.map (fun Q => Q.slot.front.counterArena.live.card) := by
    rw [cards]
    simpa only [walkSeed_card,walkSeed_widths,List.length_nil,walkRegisters,List.length_range'] using authorCounterFull
  obtain ⟨Q,hQ,card⟩ := List.mem_map.mp member
  refine ⟨Q,hQ,Finset.eq_of_subset_of_card_le Q.slot.front.counterArena.bounded ?_⟩
  rw [card]
  simp [arenaWires]

end ECDSAAdd.Arithmetic.Paper935
