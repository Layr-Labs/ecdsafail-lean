import ECDSAAdd.Arithmetic.Paper935.HistoricalSlotStaticTotal

namespace ECDSAAdd.Arithmetic.Paper935

/-- Persistent history growth preserves an arbitrary separated owned frame. -/
theorem planHistoryGrow_frame (A B : Arena) (record grown fixed : List Wire) (capacity : Nat)
    (compiled : planHistoryGrow A record capacity=some (B,grown))
    (distinct : (fixed++record).Nodup) (owned : (fixed++record).toFinset⊆A.live) :
    (fixed++grown).Nodup ∧ (fixed++grown).toFinset⊆B.live ∧
    B.live.card=A.live.card+(capacity-record.length) := by
  unfold planHistoryGrow at compiled
  obtain ⟨⟨C,extra⟩,hb,h⟩ := Option.bind_eq_some_iff.mp compiled
  cases h
  have layout := A.borrowMany_append B _ extra (fixed++record) hb distinct owned
  exact ⟨by simpa only [List.append_assoc] using layout.1,
    by simpa only [List.append_assoc] using layout.2,(A.borrowMany_live B _ extra hb).2⟩

/-- The actual historical slot returns the grown persistent layout for the next
compiler call; detector work is not retained in this arena. -/
theorem compileHistoricalSlot_exit_geometry (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (compiled : compileCheckedHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q)
    (distinct : (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.slot.front.exitArena.live) :
    (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup ∧
    (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.historyArena.live ∧
    Q.historyArena.live.card=Q.slot.front.exitArena.live.card+(capacity-record.length) := by
  have hc := (compileCheckedHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q compiled).1
  have slot := compileHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q hc
  have hh := compileGrowingHistory_contract Q.slot.front.exitArena Q.historyArena Q.detectorArena record Q.detectorWork capacity
    F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen F.counter
    (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history slot.2.2.2.2.2
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
