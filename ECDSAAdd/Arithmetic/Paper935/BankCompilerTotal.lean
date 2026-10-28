import ECDSAAdd.Arithmetic.Paper935.WindowRowsTotal

namespace ECDSAAdd.Arithmetic.Paper935

/-- Widths of the actual compiled bank are pure public layout facts. -/
theorem compileBankResize_widths (A C : Arena) (b out : WindowBank) (width : RowWindow) (p : Program)
    (h : compileBankResize A b width=some (C,out,p)) : out.Widths width := by
  have hc := compileBankResize_contract A C b out width p h
  have widths := planWindowRows_widths (b.requests width) A C out.rows p hc
  simpa only [WindowBank.Widths,WindowBank.rows,WindowBank.requests,List.map_cons,List.map_nil,
    List.cons.injEq,and_true] using widths

/-- Actual four-row allocation and packing succeeds under separated ownership
and a conservative sum of positive growth, retaining external registers. -/
theorem compileBankResize_static_exists (A : Arena) (b : WindowBank) (width : RowWindow) (fixed : List Wire)
    (distinct : (fixed++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (fixed++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (budget : A.live.card+rowGrowth (b.requests width)≤935) :
    ∃ C out p,compileBankResize A b width=some (C,out,p) ∧ out.Widths width ∧
      (fixed++out.rows.flatMap WindowRow.wires).Nodup ∧
      (fixed++out.rows.flatMap WindowRow.wires).toFinset⊆C.live ∧
      C.live.card≤A.live.card+rowGrowth (b.requests width) := by
  have rowsEq : (b.requests width).map Prod.fst=b.rows := rfl
  obtain ⟨C,rows,p,planned,geometry,ownership,card⟩ := planWindowRows_exists (b.requests width) A fixed
    (by simpa only [rowsEq] using distinct) (by simpa only [rowsEq] using owned) budget
  have len := planWindowRows_length (b.requests width) A C rows p planned
  obtain ⟨out,packed⟩ := bankOfRows_exists rows (by simpa [WindowBank.requests] using len)
  have compiled : compileBankResize A b width=some (C,out,p) := by
    simp [compileBankResize,planned,packed]
  have actual := bankOfRows_contract rows out packed
  exact ⟨C,out,p,compiled,compileBankResize_widths A C b out width p compiled,
    by simpa only [actual] using geometry,by simpa only [actual] using ownership,card⟩

end ECDSAAdd.Arithmetic.Paper935
