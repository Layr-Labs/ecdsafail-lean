import ECDSAAdd.Arithmetic.Paper935.SlotFrontGeometry

namespace ECDSAAdd.Arithmetic.Paper935

private theorem remove_middle_nodup (a b c : List Wire) (h : (a++b++c).Nodup) : (a++c).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hc := List.nodup_iff_count.mp h q
  simp only [List.count_append] at hc ⊢
  omega

private theorem remove_middle_owned (A : Arena) (a b c : List Wire) (h : (a++b++c).toFinset⊆A.live) :
    (a++c).toFinset⊆A.live := by
  intro q hq
  apply h
  simp only [List.mem_toFinset,List.mem_append] at hq ⊢
  exact hq.elim (fun h => Or.inl (Or.inl h)) Or.inr

/-- All arithmetic-front compiler and gate/address checks follow from public
row geometry and capacity; no input-state execution result is assumed. -/
theorem compileSlotFront_checked_exists (A : Arena) (b : WindowBank) (before addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (external : List Wire)
    (widths : b.Widths before)
    (distinct : (F.wires++external++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++external++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (pairFG : addWidth.f=addWidth.g) (pairV : addWidth.gv=addWidth.fv)
    (gPositive : 0<addWidth.g) (vPositive : 0<addWidth.fv)
    (counterNonempty : F.counter≠[]) (exitPositive : 0<exitWidth.fv)
    (paddingBudget : A.live.card+before.growth addWidth≤935)
    (resizeBudget : (A.live.card+addWidth.payload-before.payload)+addWidth.growth exitWidth≤935)
    (counterBudget : (A.live.card+exitWidth.payload-before.payload)+(2*F.counter.length-1)≤935) :
    ∃ P,compileSlotFront A b addWidth exitWidth F=some P ∧ P.PhysicalChecks F ∧
      P.exitBank.Widths exitWidth ∧
      (F.wires++external++P.exitBank.rows.flatMap WindowRow.wires).Nodup ∧
      (F.wires++external++P.exitBank.rows.flatMap WindowRow.wires).toFinset⊆P.exitArena.live ∧
      P.exitArena.live.card+before.payload=A.live.card+exitWidth.payload := by
  obtain ⟨P,compiled,exitWidths,exitDistinct,exitOwned,card,addDistinct,addOwned⟩ :=
    compileSlotFront_exists A b before addWidth exitWidth F external widths distinct owned
      pairFG pairV gPositive vPositive paddingBudget resizeBudget counterBudget
  have contract := compileSlotFront_contract A b addWidth exitWidth F P compiled
  have checks := contract.checks_of_geometry P A b addWidth exitWidth F counterNonempty
    (remove_middle_nodup _ external _ addDistinct) (remove_middle_owned P.addArena _ external _ addOwned)
    (remove_middle_nodup _ external _ exitDistinct) (remove_middle_owned P.exitArena _ external _ exitOwned)
    (by intro he; have hv := exitWidths.2.2.1; rw [he] at hv; simp at hv; omega)
  exact ⟨P,compiled,checks,exitWidths,exitDistinct,exitOwned,card⟩

end ECDSAAdd.Arithmetic.Paper935
