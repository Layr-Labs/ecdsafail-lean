import ECDSAAdd.Arithmetic.Paper935.WalkDecoderTotal
import ECDSAAdd.Arithmetic.Paper935.SlotDecoderResources

namespace ECDSAAdd.Arithmetic.Paper935

theorem compileHistoricalWalk_decoder_support (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : compileHistoricalWalk F probeWidth A b record requests=some slots)
    (counterWidth : F.counter.length=7)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (budgets : historicalBudgets F probeWidth A.live.card (bankWidths b) record.length requests)
    (decoderBudget : decoderBudgets A.live.card (bankWidths b) record.length requests) :
    ∀ Q∈slots,∀ (p : Int) (i : Nat),wires (actualHistoryDecoder F p i Q)⊆arenaWires := by
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
      (by simpa only [hc,wc,len] using decoderBudget.2)
    intro P hp p i
    rcases List.mem_cons.mp hp with hp|hp
    · subst P
      have geometry := decoderViews_geometry Q.historyArena F Q.slot.front.exitBank Q.history.record grown.1 grown.2.1
      have port := compileHistoricalSlot_port _ _ _ _ _ _ _ _ _ _ _ checked
      have bound : Q.historyArena.live.card+rowGrowth
          (Q.slot.front.exitBank.requests Q.slot.front.exitBank.decoderWidth)+11≤935 := by
        rw [decoder_rowGrowth,hc,exitWidths.1,exitWidths.2.2.1]
        have h := decoderBudget.1
        omega
      obtain ⟨D,hD⟩ := compileSlotDecoder_exists F Q counterWidth
        (by simpa only [port] using geometry.1) (by simpa only [port] using geometry.2) bound
      rw [actualHistoryDecoder_of_compiled F Q D hD p i]
      exact compileSlotDecoder_program_support F Q D hD port grown.1 grown.2.1 (by omega) p i
    · exact tail P hp p i

attribute [local irreducible] historicalBudgets decoderBudgets

theorem compileAuthorWalk_decoder_support (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots) :
    ∀ Q∈slots,∀ (p : Int) (i : Nat),wires (actualHistoryDecoder walkRegisters p i Q)⊆arenaWires := by
  apply compileHistoricalWalk_decoder_support walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests
    slots compiled (by decide) walkSeed_distinct walkSeed_owned
  · simpa only [walkSeed_card,walkSeed_widths,List.length_nil] using authorHistoricalBudgets
  · simpa only [walkSeed_card,walkSeed_widths,List.length_nil] using authorDecoderBudgets

end ECDSAAdd.Arithmetic.Paper935
