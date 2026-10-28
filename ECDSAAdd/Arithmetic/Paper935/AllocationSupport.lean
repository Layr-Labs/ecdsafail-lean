import ECDSAAdd.Arithmetic.Paper935.CounterFullArena

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

private theorem growRow_targets (sign : Wire) (extra : List Wire) :
    extra.toFinset⊆wires (growRow sign extra) := by
  induction extra with
  | nil => simp
  | cons q qs ih =>
    intro w hw
    simp only [List.mem_toFinset,List.mem_cons] at hw
    simp only [growRow,List.flatMap_cons,resizeBit,List.singleton_append,wires,Instr.wires]
    rcases hw with rfl | hw
    · simp
    · exact Finset.mem_union_right _ (ih (List.mem_toFinset.mpr hw))

/-- A site removed from live ownership is touched by an actual resize gate. -/
theorem planRowResize_live_support (A B : Arena) (r out : WindowRow) (width : Nat) (p : Program)
    (compiled : planRowResize A r width=some (B,out,p)) : A.live⊆B.live∪wires p := by
  unfold planRowResize at compiled
  split at compiled
  next valid =>
    split at compiled
    next grows =>
      obtain ⟨⟨C,qs⟩,borrow,h⟩ := Option.bind_eq_some_iff.mp compiled
      cases h
      rw [(A.borrowMany_live B _ qs borrow).1]
      exact Finset.subset_union_left.trans Finset.subset_union_left
    next shrinks =>
      cases compiled
      intro q hq
      by_cases removed : q∈(r.payload.drop width).toFinset
      · apply Finset.mem_union_right
        rw [shrinkRow,wires_reverse]
        exact growRow_targets r.sign _ removed
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hq,removed⟩)
  next invalid => simp at compiled

theorem planWindowRows_live_support (requests : List (WindowRow × Nat)) (A B : Arena)
    (outs : List WindowRow) (p : Program)
    (compiled : planWindowRows A requests=some (B,outs,p)) : A.live⊆B.live∪wires p := by
  induction requests generalizing A B outs p with
  | nil =>
    simp only [planWindowRows,Option.some.injEq,Prod.mk.injEq] at compiled
    rcases compiled with ⟨rfl,rfl,rfl⟩
    exact Finset.subset_union_left
  | cons request rest ih =>
    rcases request with ⟨r,width⟩
    unfold planWindowRows at compiled
    split at compiled
    next valid =>
      obtain ⟨⟨C,row,front⟩,hc,h⟩ := Option.bind_eq_some_iff.mp compiled
      obtain ⟨⟨D,rows,back⟩,hd,h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      next exitValid =>
        cases h
        have first := planRowResize_live_support A C r row width front hc
        have tail := ih C B rows back hd
        intro q hq
        rw [wires_append]
        rcases Finset.mem_union.mp (first hq) with live | touched
        · rcases Finset.mem_union.mp (tail live) with live | touched
          · exact Finset.mem_union_left _ live
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ touched)
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ touched)
      next invalid => simp at h
    next invalid => simp at compiled

theorem compileBankResize_live_support (A B : Arena) (b out : WindowBank) (w : RowWindow)
    (p : Program) (compiled : compileBankResize A b w=some (B,out,p)) : A.live⊆B.live∪wires p :=
  planWindowRows_live_support _ _ _ _ _ (compileBankResize_contract A B b out w p compiled)

private theorem counter_scratch_support (active swap : Wire) (zero z carry : List Wire)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length) :
    (zero++carry).toFinset⊆wires (counterUpdateInverse active swap zero z carry) := by
  intro q hq
  rw [counterUpdateInverse,wires_append,wires_append]
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  rw [negateSigned,wires_append]
  apply Finset.mem_union_right
  rw [ECDSAAdd.Arithmetic.addInPlace_wires zero z carry active hz hc]
  simp only [List.mem_toFinset,List.mem_append] at hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto

/-- Padding, resizing, and every allocated counter site occur in the actual
arithmetic inverse. This is a lower support bound, not just containment. -/
theorem SlotFront.inverse_support_lower (P : SlotFront) (F : SlotRegisters)
    (hz : P.zero.length=F.counter.length) (hc : P.carry.length+1=F.counter.length) :
    wires P.padding∪wires P.resizing∪(P.zero++P.carry).toFinset⊆wires (P.inverse F) := by
  have scratch := counter_scratch_support P.layout.active P.layout.q P.zero F.counter P.carry hz hc
  intro q hq
  simp only [SlotFront.inverse,RoutedBankLayout.retiredWindowInverse,RoutedBankLayout.taggedWindowInverse,
    RoutedBankLayout.windowStepInverse,wires_append,wires_reverse,Finset.mem_union]
  simp only [Finset.mem_union] at hq
  rcases hq with (padding | resizing) | temp
  · tauto
  · tauto
  · have hit := scratch temp
    tauto

private theorem reserve_live (A B : Arena) (qs : Finset Wire) (h : A.reserve qs=some B) :
    B.live=A.live∪qs := by
  unfold Arena.reserve at h
  split at h
  next valid => cases h; rfl
  next invalid => simp at h

/-- Entry ownership and during-counter ownership are accounted for by the exit
arena or actual inverse support. No allocator-only disappearance is allowed. -/
theorem SlotFront.Compiled.live_support (P : SlotFront) (A : Arena) (b : WindowBank)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters)
    (compiled : P.Compiled A b addWidth exitWidth F) (nonempty : 1≤F.counter.length) :
    A.live⊆P.exitArena.live∪wires (P.inverse F) ∧
    P.counterArena.live⊆P.exitArena.live∪wires (P.inverse F) := by
  have first := compileBankResize_live_support _ _ _ _ _ _ compiled.padding
  have second := compileBankResize_live_support _ _ _ _ _ _ compiled.resizing
  have counter := planCounterScratch_contract _ _ _ _ _ nonempty compiled.counter
  have support := P.inverse_support_lower F counter.1 counter.2.1
  constructor
  · intro q hq
    rcases Finset.mem_union.mp (first hq) with live | touched
    · rcases Finset.mem_union.mp (second live) with live | touched
      · exact Finset.mem_union_left _ live
      · exact Finset.mem_union_right _ (support (Finset.mem_union_left _ (Finset.mem_union_right _ touched)))
    · exact Finset.mem_union_right _ (support (Finset.mem_union_left _ (Finset.mem_union_left _ touched)))
  · rw [reserve_live _ _ _ counter.2.2.2]
    intro q hq
    rcases Finset.mem_union.mp hq with live | temp
    · exact Finset.mem_union_left _ live
    · exact Finset.mem_union_right _ (support (Finset.mem_union_right _ temp))

end ECDSAAdd.Arithmetic.Paper935
