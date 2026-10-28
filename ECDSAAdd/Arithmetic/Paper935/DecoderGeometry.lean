import ECDSAAdd.Arithmetic.Paper935.SlotDecoderTotal
import ECDSAAdd.Arithmetic.Paper935.HistoryGrowthGeometry

namespace ECDSAAdd.Arithmetic.Paper935

theorem decoderViews_geometry (A : Arena) (F : SlotRegisters) (b : WindowBank) (record : List Wire)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live) :
    ([F.one,F.frozen,F.parity]++F.counter++b.rows.flatMap WindowRow.wires).Nodup ∧
    ([F.one,F.frozen,F.parity]++F.counter++b.rows.flatMap WindowRow.wires).toFinset⊆A.live := by
  have counts (q : Wire) :
      ([F.one,F.frozen,F.parity]++F.counter++b.rows.flatMap WindowRow.wires).count q≤
      (F.wires++record++b.rows.flatMap WindowRow.wires).count q := by
    simp only [SlotRegisters.wires,List.count_append,List.count_cons,List.count_nil]
    omega
  constructor
  · apply List.nodup_iff_count.mpr
    intro q
    exact (counts q).trans (List.nodup_iff_count.mp distinct q)
  · intro q hq
    apply owned
    simp only [List.mem_toFinset] at hq ⊢
    exact List.count_pos_iff.mp (lt_of_lt_of_le (List.count_pos_iff.mpr hq) (counts q))

theorem compileHistoricalSlot_port (A : Arena) (b : WindowBank) (record : List Wire)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (armed : Bool)
    (probeWidth offset capacity : Nat) (Q : HistoricalSlot)
    (h : compileHistoricalSlot A b record addWidth exitWidth F armed probeWidth offset capacity=some Q) :
    Q.history.port=F.parity := by
  have hc := compileHistoricalSlot_contract A b record addWidth exitWidth F armed probeWidth offset capacity Q h
  have hh := compileGrowingHistory_contract Q.slot.front.exitArena Q.historyArena Q.detectorArena record
    Q.detectorWork capacity F.one F.work0 F.work1 (F.counter.getLastD 0) F.active F.parity F.frozen F.counter
    (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history hc.2.2.2.2.2
  exact (compileHistory_identity _ _ _ _ _ _ _ _ _ _ _ _ hh.2.2).2.2.2.2.2

theorem decoder_rowGrowth (b : WindowBank) :
    rowGrowth (b.requests b.decoderWidth)=(6-b.f.payload.length)+(12-b.fv.payload.length) := by
  simp only [rowGrowth,WindowBank.requests,WindowBank.decoderWidth]
  omega

end ECDSAAdd.Arithmetic.Paper935
