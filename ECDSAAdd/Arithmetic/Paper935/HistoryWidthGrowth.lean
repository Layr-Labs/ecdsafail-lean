import ECDSAAdd.Arithmetic.Paper935.HistoryGrowthGeometry
import ECDSAAdd.Arithmetic.Paper935.HistoricalSlotWidthStaticTotal

namespace ECDSAAdd.Arithmetic.Paper935

/-- The actual historical slot returns the grown persistent layout for the next
compiler call; detector work is not retained in this arena. -/
theorem compileHistoricalSlotWidth_exit_geometry (hw : Nat) (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (compiled : compileCheckedHistoricalSlotWidth hw A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (distinct : (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.slot.front.exitArena.live) :
    (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup ∧
    (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.historyArena.live ∧
    Q.historyArena.live.card=Q.slot.front.exitArena.live.card+(capacity-record.length) := by
  have hc := (compileCheckedHistoricalSlotWidth_contract hw A b record addWidth exitWidth F armed probeWidth offset capacity Q compiled).1
  have slot := compileHistoricalSlotWidth_contract hw A b record addWidth exitWidth F armed probeWidth offset capacity Q hc
  have hh := compileGrowingHistory_contract Q.slot.front.exitArena Q.historyArena Q.detectorArena record Q.detectorWork capacity
    F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen F.counter
    (Q.slot.front.exitBank.fv.wires.drop 1 |>.take hw) Q.history slot.2.2.2.2.2
  have dn : (F.wires++Q.slot.front.exitBank.rows.flatMap WindowRow.wires++record).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp distinct q
    simp only [List.count_append] at h ⊢
    omega
  have ow : (F.wires++Q.slot.front.exitBank.rows.flatMap WindowRow.wires++record).toFinset⊆Q.slot.front.exitArena.live := by
    simpa only [List.toFinset_append,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm] using owned
  have grown := planHistoryGrow_frame Q.slot.front.exitArena Q.historyArena record Q.history.record
    (F.wires++Q.slot.front.exitBank.rows.flatMap WindowRow.wires) capacity hh.1 dn ow
  refine ⟨?_,?_,grown.2.2⟩
  · apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp grown.1 q
    simp only [List.count_append] at h ⊢
    omega
  · simpa only [List.toFinset_append,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm] using grown.2.1

end ECDSAAdd.Arithmetic.Paper935
