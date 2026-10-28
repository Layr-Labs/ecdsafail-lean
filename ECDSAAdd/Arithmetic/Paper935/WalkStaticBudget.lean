import ECDSAAdd.Arithmetic.Paper935.HistoryGrowthGeometry
import ECDSAAdd.Arithmetic.Paper935.HistoricalWalkCompiler

namespace ECDSAAdd.Arithmetic.Paper935

/-- Pure public sufficient conditions for the actual allocation sequence. -/
structure HistoricalStaticBudget (F : SlotRegisters) (probeWidth live : Nat)
    (before : RowWindow) (recordLength : Nat) (r : HistoricalRequest) : Prop where
  padding : live+before.growth before.addPad≤935
  resize : (live+before.addPad.payload-before.payload)+before.addPad.growth (historyWindow r.exitWidth)≤935
  counter : (live+(historyWindow r.exitWidth).payload-before.payload)+(2*F.counter.length-1)≤935
  probePositive : r.armed=true → 0<probeWidth
  post : r.armed=true → (live+(historyWindow r.exitWidth).payload-before.payload)+
    max (probeWidth+probeChunkCount ((historyWindow r.exitWidth).g+1) probeWidth) (F.offset.length+1)≤935
  offset : r.armed=true → r.offset<2^F.offset.length
  history : (live+(historyWindow r.exitWidth).payload-before.payload)+(r.capacity-recordLength)+max F.counter.length 8≤935

def historicalBudgets (F : SlotRegisters) (probeWidth : Nat) :
    Nat → RowWindow → Nat → List HistoricalRequest → Prop
  | _,_,_,[] => True
  | live,before,n,r::rs => HistoricalStaticBudget F probeWidth live before n r ∧
      historicalBudgets F probeWidth
        ((live+(historyWindow r.exitWidth).payload-before.payload)+(r.capacity-n))
        (historyWindow r.exitWidth) (max r.capacity n) rs

instance historicalStaticBudgetDecidable (F : SlotRegisters) (probeWidth live : Nat)
    (before : RowWindow) (n : Nat) (r : HistoricalRequest) :
    Decidable (HistoricalStaticBudget F probeWidth live before n r) :=
  decidable_of_iff
    (live+before.growth before.addPad≤935 ∧
    (live+before.addPad.payload-before.payload)+before.addPad.growth (historyWindow r.exitWidth)≤935 ∧
    (live+(historyWindow r.exitWidth).payload-before.payload)+(2*F.counter.length-1)≤935 ∧
    (r.armed=true → 0<probeWidth) ∧
    (r.armed=true → (live+(historyWindow r.exitWidth).payload-before.payload)+
      max (probeWidth+probeChunkCount ((historyWindow r.exitWidth).g+1) probeWidth) (F.offset.length+1)≤935) ∧
    (r.armed=true → r.offset<2^F.offset.length) ∧
    (live+(historyWindow r.exitWidth).payload-before.payload)+(r.capacity-n)+max F.counter.length 8≤935) ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩,
    fun h => ⟨h.padding,h.resize,h.counter,h.probePositive,h.post,h.offset,h.history⟩⟩

instance historicalBudgetsDecidable (F : SlotRegisters) (probeWidth live : Nat)
    (before : RowWindow) (n : Nat) (requests : List HistoricalRequest) :
    Decidable (historicalBudgets F probeWidth live before n requests) := by
  induction requests generalizing live before n with
  | nil => unfold historicalBudgets; infer_instance
  | cons r rs ih => unfold historicalBudgets; exact instDecidableAnd

/-- Public numerical budgets and persistent geometry imply successful actual
compilation of every slot in the list. -/
theorem compileHistoricalWalk_static_exists (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (counterNonempty : F.counter≠[])
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (budgets : historicalBudgets F probeWidth A.live.card (bankWidths b) record.length requests) :
    ∃ slots,compileHistoricalWalk F probeWidth A b record requests=some slots := by
  induction requests generalizing A b record with
  | nil => exact ⟨[],rfl⟩
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
    obtain ⟨rest,hr⟩ := ih Q.historyArena Q.slot.front.exitBank Q.history.record grown.1 grown.2.1
      (by simpa only [hc,wc,len] using budgets.2)
    exact ⟨Q::rest,by simp [compileHistoricalWalk,hq,hr]⟩

end ECDSAAdd.Arithmetic.Paper935
