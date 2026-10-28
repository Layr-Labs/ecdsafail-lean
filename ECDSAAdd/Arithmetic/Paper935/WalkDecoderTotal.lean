import ECDSAAdd.Arithmetic.Paper935.DecoderGeometry
import ECDSAAdd.Arithmetic.Paper935.AuthorWalkBudgets

namespace ECDSAAdd.Arithmetic.Paper935

/-- Public capacity accounting for sign padding and the reused eleven-wire
pool, while retaining the grown persistent history. -/
def decoderBudgets : Nat → RowWindow → Nat → List HistoricalRequest → Prop
  | _,_,_,[] => True
  | live,before,n,r::rs =>
    let w := historyWindow r.exitWidth
    let next := (live+w.payload-before.payload)+(r.capacity-n)
    next+(6-w.f)+(12-w.fv)+11≤935 ∧
      decoderBudgets next w (max r.capacity n) rs

instance decoderBudgetsDecidable (live : Nat) (before : RowWindow) (n : Nat)
    (requests : List HistoricalRequest) : Decidable (decoderBudgets live before n requests) := by
  induction requests generalizing live before n with
  | nil => unfold decoderBudgets; infer_instance
  | cons r rs ih => unfold decoderBudgets; exact instDecidableAnd

theorem authorDecoderBudgets : decoderBudgets 794 initialWindow 0 authorHistoricalRequests := by
  decide +kernel

theorem compileHistoricalWalk_decoders (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (compiled : compileHistoricalWalk F probeWidth A b record requests=some slots)
    (counterWidth : F.counter.length=7)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (budgets : historicalBudgets F probeWidth A.live.card (bankWidths b) record.length requests)
    (decoderBudget : decoderBudgets A.live.card (bankWidths b) record.length requests) :
    ∀ Q∈slots,∃ D,compileSlotDecoder F Q=some D := by
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
    intro P hp
    rcases List.mem_cons.mp hp with hp|hp
    · subst P
      have geometry := decoderViews_geometry Q.historyArena F Q.slot.front.exitBank Q.history.record grown.1 grown.2.1
      have port := compileHistoricalSlot_port _ _ _ _ _ _ _ _ _ _ _ checked
      apply compileSlotDecoder_exists F Q counterWidth
      · simpa only [port] using geometry.1
      · simpa only [port] using geometry.2
      · rw [decoder_rowGrowth,hc]
        have wf : Q.slot.front.exitBank.f.payload.length=(historyWindow r.exitWidth).f := exitWidths.1
        have wv : Q.slot.front.exitBank.fv.payload.length=(historyWindow r.exitWidth).fv := exitWidths.2.2.1
        rw [wf,wv]
        have h := decoderBudget.1
        omega
    · exact tail P hp

attribute [local irreducible] historicalBudgets decoderBudgets

theorem compileAuthorWalk_decoders (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots) :
    ∀ Q∈slots,∃ D,compileSlotDecoder walkRegisters Q=some D := by
  apply compileHistoricalWalk_decoders walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests
    slots compiled (by decide) walkSeed_distinct walkSeed_owned
  · simpa only [walkSeed_card,walkSeed_widths,List.length_nil] using authorHistoricalBudgets
  · simpa only [walkSeed_card,walkSeed_widths,List.length_nil] using authorDecoderBudgets

end ECDSAAdd.Arithmetic.Paper935
