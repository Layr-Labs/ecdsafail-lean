import ECDSAAdd.Arithmetic.Paper935.SlotViewsGeometry
import ECDSAAdd.Arithmetic.Paper935.ProbeChunkCount

namespace ECDSAAdd.Arithmetic.Paper935

/-- The full public arithmetic slot compiles from public widths, owned geometry
and static pool budgets, without a front-compiler success premise. -/
theorem compilePublicSlot_static_exists (A : Arena) (b : WindowBank) (before addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (external : List Wire) (armed : Bool) (probeWidth offset : Nat)
    (widths : b.Widths before)
    (distinct : (F.wires++external++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++external++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (pairFG : addWidth.f=addWidth.g) (pairV : addWidth.gv=addWidth.fv)
    (gPositive : 0<addWidth.g) (vPositive : 0<addWidth.fv)
    (counterNonempty : F.counter≠[]) (exitPositive : 0<exitWidth.fv)
    (paddingBudget : A.live.card+before.growth addWidth≤935)
    (resizeBudget : (A.live.card+addWidth.payload-before.payload)+addWidth.growth exitWidth≤935)
    (counterBudget : (A.live.card+exitWidth.payload-before.payload)+(2*F.counter.length-1)≤935)
    (probePositive : armed=true → 0<probeWidth)
    (postBudget : armed=true → (A.live.card+exitWidth.payload-before.payload)+
      max (probeWidth+probeChunkCount (exitWidth.g+1) probeWidth) (F.offset.length+1)≤935)
    (offsetFits : armed=true → offset<2^F.offset.length) :
    ∃ P,compileCheckedPublicSlot A b addWidth exitWidth F armed probeWidth offset=some P ∧
      P.front.exitBank.Widths exitWidth ∧
      (F.wires++external++P.front.exitBank.rows.flatMap WindowRow.wires).Nodup ∧
      (F.wires++external++P.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆P.front.exitArena.live ∧
      P.front.exitArena.live.card+before.payload=A.live.card+exitWidth.payload := by
  obtain ⟨front,compiled,physical,exitWidths,exitDistinct,exitOwned,card⟩ :=
    compileSlotFront_checked_exists A b before addWidth exitWidth F external widths distinct owned
      pairFG pairV gPositive vPositive counterNonempty exitPositive paddingBudget resizeBudget counterBudget
  have views := postViews_geometry front.exitArena F front.exitBank external exitDistinct exitOwned
  have existsSlot : ∃ P,compileCheckedPublicSlot A b addWidth exitWidth F armed probeWidth offset=some P ∧ P.front=front := by
    cases armed with
    | true =>
      apply compileCheckedPublicSlot_armed_exists A b addWidth exitWidth F probeWidth offset front compiled physical
        (probePositive rfl) views.1 views.2 _ (offsetFits rfl)
      rw [postPoolSize_public _ _ _ (probePositive rfl)]
      have glen : front.exitBank.g.wires.length=exitWidth.g+1 := by
        simp only [WindowRow.wires,List.length_append,List.length_singleton]
        rw [exitWidths.2.1]
      rw [glen]
      have hc : front.exitArena.live.card=A.live.card+exitWidth.payload-before.payload := by omega
      rw [hc]
      exact postBudget rfl
    | false =>
      have fa : F.frozen≠F.active := by
        intro he
        have hc := List.nodup_iff_count.mp views.1 F.active
        simp only [List.count_append,List.count_cons,List.count_nil,he,beq_self_eq_true,ite_true] at hc
        omega
      have wa : F.work1≠F.active := by
        intro he
        have hc := List.nodup_iff_count.mp views.1 F.active
        simp only [List.count_append,List.count_cons,List.count_nil,he,beq_self_eq_true,ite_true] at hc
        omega
      apply compileCheckedPublicSlot_unarmed_exists A b addWidth exitWidth F probeWidth offset front compiled physical fa wa
      intro q hq
      apply front.exitArena.bounded
      apply views.2
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl <;> simp
  obtain ⟨P,hp,hfront⟩ := existsSlot
  exact ⟨P,hp,by simpa [hfront] using exitWidths,by simpa [hfront] using exitDistinct,
    by simpa [hfront] using exitOwned,by simpa [hfront] using card⟩

end ECDSAAdd.Arithmetic.Paper935
