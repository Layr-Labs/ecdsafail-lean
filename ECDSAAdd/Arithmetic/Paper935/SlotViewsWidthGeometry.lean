import ECDSAAdd.Arithmetic.Paper935.SlotFrontCheckedTotal

namespace ECDSAAdd.Arithmetic.Paper935

private theorem geometry_of_counts (A : Arena) (small large : List Wire)
    (counts : ∀ q,small.count q≤large.count q)
    (distinct : large.Nodup) (owned : large.toFinset⊆A.live) :
    small.Nodup ∧ small.toFinset⊆A.live := by
  constructor
  · apply List.nodup_iff_count.mpr
    intro q
    exact (counts q).trans (List.nodup_iff_count.mp distinct q)
  · intro q hq
    apply owned
    simp only [List.mem_toFinset] at hq ⊢
    exact List.count_pos_iff.mp (lt_of_lt_of_le (List.count_pos_iff.mpr hq) (counts q))

/-- Counter and coefficient history views inherit the full layout's geometry. -/
theorem historyViewsWidth_geometry (hw : Nat) (A : Arena) (F : SlotRegisters) (b : WindowBank) (record : List Wire)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live) :
    ([F.one,F.work0,F.work1,F.active,F.parity,F.frozen]++F.counter++
      (b.fv.wires.drop 1 |>.take hw)++record).Nodup ∧
    ([F.one,F.work0,F.work1,F.active,F.parity,F.frozen]++F.counter++
      (b.fv.wires.drop 1 |>.take hw)++record).toFinset⊆A.live := by
  apply geometry_of_counts A _ _ _ distinct owned
  intro q
  have h := ((List.take_sublist hw (b.fv.wires.drop 1)).trans (List.drop_sublist 1 b.fv.wires)).count_le q
  simp only [SlotRegisters.wires,WindowBank.rows,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.count_append,List.count_cons,List.count_nil]
  omega

end ECDSAAdd.Arithmetic.Paper935
