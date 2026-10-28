import ECDSAAdd.Arithmetic.Paper935.RowResizeCard

namespace ECDSAAdd.Arithmetic.Paper935

/-- The arithmetic row-view rotation is a permutation of physical addresses. -/
theorem RoutedBankLayout.after_count (L : RoutedBankLayout) (q : Wire) :
    (L.after.rows.flatMap WindowRow.wires).count q=(L.before.rows.flatMap WindowRow.wires).count q := by
  simp only [after,before,WindowBank.rows,WindowRow.wires,List.flatMap_cons,List.flatMap_nil,
    List.count_append,List.count_cons,List.count_nil]
  omega

theorem RoutedBankLayout.after_sites (L : RoutedBankLayout) :
    (L.after.rows.flatMap WindowRow.wires).toFinset=(L.before.rows.flatMap WindowRow.wires).toFinset := by
  ext q
  simp only [List.mem_toFinset,←List.count_pos_iff,L.after_count]

/-- Routing keeps an external ownership frame intact without running the circuit. -/
theorem RoutedBankLayout.after_geometry (L : RoutedBankLayout) (A : Arena) (fixed : List Wire)
    (distinct : (fixed++L.before.rows.flatMap WindowRow.wires).Nodup)
    (owned : (fixed++L.before.rows.flatMap WindowRow.wires).toFinset⊆A.live) :
    (fixed++L.after.rows.flatMap WindowRow.wires).Nodup ∧
    (fixed++L.after.rows.flatMap WindowRow.wires).toFinset⊆A.live := by
  constructor
  · apply List.nodup_iff_count.mpr
    intro q
    simpa only [List.count_append,L.after_count] using List.nodup_iff_count.mp distinct q
  · simpa only [List.toFinset_append,L.after_sites] using owned

/-- Public expression for positive payload growth of a four-row resize. -/
def RowWindow.growth (before after : RowWindow) : Nat :=
  (after.f-before.f)+(after.g-before.g)+(after.fv-before.fv)+(after.gv-before.gv)

theorem rowGrowth_of_widths (b : WindowBank) (before after : RowWindow) (widths : b.Widths before) :
    rowGrowth (b.requests after)=before.growth after := by
  rcases widths with ⟨hf,hg,hv,hr⟩
  simp only [rowGrowth,WindowBank.requests,RowWindow.growth,hf,hg,hv,hr,Nat.add_zero]
  omega

/-- Exact compiled-bank allocation balance, expressed in public payload widths. -/
theorem compileBankResize_card (A C : Arena) (b out : WindowBank) (before after : RowWindow) (p : Program)
    (widths : b.Widths before) (compiled : compileBankResize A b after=some (C,out,p)) :
    C.live.card+before.payload=A.live.card+after.payload := by
  have hc := compileBankResize_contract A C b out after p compiled
  have card := planWindowRows_card (b.requests after) A C out.rows p hc
  rcases widths with ⟨hf,hg,hv,hr⟩
  simp only [WindowBank.requests,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hf,hg,hv,hr,
    Nat.add_zero] at card
  unfold RowWindow.payload
  omega

end ECDSAAdd.Arithmetic.Paper935
