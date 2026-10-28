import ECDSAAdd.Arithmetic.Paper935.RoutedGeometry

namespace ECDSAAdd.Arithmetic.Paper935

/-- Actual padding, routed arithmetic views, exit resize and counter-scratch
allocation all succeed from static row ownership and public capacity budgets.
External registers (such as the history record) remain owned and separated. -/
theorem compileSlotFront_exists (A : Arena) (b : WindowBank) (before addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (external : List Wire)
    (widths : b.Widths before)
    (distinct : (F.wires++external++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++external++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (pairFG : addWidth.f=addWidth.g) (pairV : addWidth.gv=addWidth.fv)
    (gPositive : 0<addWidth.g) (vPositive : 0<addWidth.fv)
    (paddingBudget : A.live.card+before.growth addWidth≤935)
    (resizeBudget : (A.live.card+addWidth.payload-before.payload)+addWidth.growth exitWidth≤935)
    (counterBudget : (A.live.card+exitWidth.payload-before.payload)+(2*F.counter.length-1)≤935) :
    ∃ P,compileSlotFront A b addWidth exitWidth F=some P ∧ P.exitBank.Widths exitWidth ∧
      (F.wires++external++P.exitBank.rows.flatMap WindowRow.wires).Nodup ∧
      (F.wires++external++P.exitBank.rows.flatMap WindowRow.wires).toFinset⊆P.exitArena.live ∧
      P.exitArena.live.card+before.payload=A.live.card+exitWidth.payload ∧
      (F.wires++external++P.addBank.rows.flatMap WindowRow.wires).Nodup ∧
      (F.wires++external++P.addBank.rows.flatMap WindowRow.wires).toFinset⊆P.addArena.live := by
  obtain ⟨B,padded,padding,pad,padWidths,padDistinct,padOwned,_⟩ :=
    compileBankResize_static_exists A b addWidth (F.wires++external) distinct owned
      (by rw [rowGrowth_of_widths b before addWidth widths]; exact paddingBudget)
  have padCard := compileBankResize_card A B b padded before addWidth padding widths pad
  have routeDistinct : (F.swap::F.parity::F.work0::F.work1::F.active::padded.rows.flatMap WindowRow.wires).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hc := List.nodup_iff_count.mp padDistinct q
    simp only [SlotRegisters.wires,List.count_append,List.count_cons,List.count_nil] at hc ⊢
    omega
  obtain ⟨L,routed⟩ := compileRoutedBank_exists F.swap F.parity F.work0 F.work1 F.active padded
    (by intro he; have hg := padWidths.2.1; rw [he] at hg; simp at hg; omega)
    (by intro he; have hv := padWidths.2.2.1; rw [he] at hv; simp at hv; omega)
    (padWidths.1.trans (pairFG.trans padWidths.2.1.symm))
    (padWidths.2.2.2.trans (pairV.trans padWidths.2.2.1.symm)) routeDistinct
  have routeContract := compileRoutedBank_contract F.swap F.parity F.work0 F.work1 F.active padded L routed
  have afterWidths := L.widths_after addWidth (by rw [routeContract.2.1]; exact padWidths)
  have afterGeometry := L.after_geometry B (F.wires++external)
    (by rw [routeContract.2.1]; exact padDistinct) (by rw [routeContract.2.1]; exact padOwned)
  obtain ⟨C,out,resizing,resize,exitWidths,exitDistinct,exitOwned,_⟩ :=
    compileBankResize_static_exists B L.after exitWidth (F.wires++external) afterGeometry.1 afterGeometry.2
      (by rw [rowGrowth_of_widths L.after addWidth exitWidth afterWidths]; omega)
  have resizeCard := compileBankResize_card B C L.after out addWidth exitWidth resizing afterWidths resize
  have finalCard : C.live.card+before.payload=A.live.card+exitWidth.payload := by omega
  obtain ⟨D,zero,carry,counter⟩ := (planCounterScratch_capacity C F.counter.length).mpr (by omega)
  let P : SlotFront := ⟨B,padded,padding,L,C,out,resizing,D,zero,carry⟩
  refine ⟨P,?_,exitWidths,exitDistinct,exitOwned,finalCard,padDistinct,padOwned⟩
  simp [compileSlotFront,pad,routed,resize,counter,P]

end ECDSAAdd.Arithmetic.Paper935
