import ECDSAAdd.Arithmetic.Paper935.SlotMathGeometry

namespace ECDSAAdd.Arithmetic.Paper935

/-- The compiled arithmetic semantics needs no separate address oracle once
static input geometry and the public allocation bounds are established. -/
theorem compileSlotFront_mathChecks (A : Arena) (b : WindowBank) (before addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (external : List Wire) (P : SlotFront)
    (compiled : compileSlotFront A b addWidth exitWidth F=some P)
    (widths : b.Widths before)
    (distinct : (F.wires++external++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++external++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (pairFG : addWidth.f=addWidth.g) (pairV : addWidth.gv=addWidth.fv)
    (gPositive : 0<addWidth.g) (vPositive : 0<addWidth.fv)
    (counterWidth : 2≤F.counter.length) (coefficientWidth : 1≤exitWidth.fv)
    (paddingBudget : A.live.card+before.growth addWidth≤935)
    (resizeBudget : (A.live.card+addWidth.payload-before.payload)+addWidth.growth exitWidth≤935)
    (counterBudget : (A.live.card+exitWidth.payload-before.payload)+(2*F.counter.length-1)≤935) :
    P.MathChecks F exitWidth := by
  obtain ⟨Q,hq,_,exitDistinct,_,_,addDistinct,addOwned⟩ :=
    compileSlotFront_exists A b before addWidth exitWidth F external widths distinct owned
      pairFG pairV gPositive vPositive paddingBudget resizeBudget counterBudget
  rw [compiled,Option.some.injEq] at hq
  subst Q
  apply (compileSlotFront_contract A b addWidth exitWidth F P compiled).mathChecks_of_geometry
    P A b addWidth exitWidth F _ _ _ counterWidth coefficientWidth
  · apply List.nodup_iff_count.mpr
    intro q
    have hc := List.nodup_iff_count.mp addDistinct q
    simp only [List.count_append] at hc ⊢
    omega
  · intro q hq
    apply addOwned
    simp only [List.mem_toFinset,List.mem_append] at hq ⊢
    exact hq.elim (fun h => Or.inl (Or.inl h)) Or.inr
  · apply List.nodup_iff_count.mpr
    intro q
    have hc := List.nodup_iff_count.mp exitDistinct q
    simp only [List.count_append] at hc ⊢
    omega

end ECDSAAdd.Arithmetic.Paper935
