import ECDSAAdd.Arithmetic.BalancedFieldCircuitProgram

set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic

namespace BalancedCleanup

theorem support (L : Layout) (hw : L.Widths) :
    wires (program L) ⊆ L.wires.toFinset := by
  have w := widths L hw
  have ns := literalConstAdd_wires L.low (L.carry.take 254) L.lower L.one negativeLiteral
  have ps := literalConstAdd_wires L.low (L.carry.take 254) L.lower L.one positiveLiteral
  have cmp := (compareLt_wires none L.y L.r L.carry L.one L.parity
    (by omega) (by unfold Layout.Widths at hw; omega)).1
  have rr := (rotate_wires L.r).2
  have cr := signComplement_wires_subset L.lower L.r
  have cy := signComplement_wires_subset L.sign L.y
  have cl := signComplement_wires_subset L.lower L.y
  have sign : wires (prepareSign L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [prepareSign,wires_append,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq
    · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,Layout.wires,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
    · have h := cr hq
      simp only [Layout.wires,Layout.r,Layout.low,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
  have view : wires (prepareCompare L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [prepareCompare,wires_append,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq|hq|hq|hq
    · rw [rr,if_neg (by omega)] at hq
      simp only [Layout.wires,Layout.r,Layout.low,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
    · simp only [wires,Instr.wires,Layout.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
    · have h := cy hq; simp only [Layout.wires,Layout.y,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
    · have h := cl hq; simp only [Layout.wires,Layout.y,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
    · simp only [wires,Instr.wires,Layout.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  have norm : wires (normalize L) ⊆ L.wires.toFinset := by
    intro q hq
    have h := ns hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    have take : q∈L.carry.take 254 → q∈L.carry := List.mem_of_mem_take
    simp only [Layout.wires,Layout.low,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
  have un : wires (unnormalize L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [unnormalize,wires_append,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq|hq
    · simp only [wires,Instr.wires,Layout.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
    · have h := ps hq
      have take : q∈L.carry.take 254 → q∈L.carry := List.mem_of_mem_take
      simp only [Layout.wires,Layout.low,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
    · simp only [wires,Instr.wires,Layout.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  intro q hq
  simp only [program,wires_append,wires_reverse,Finset.mem_union,or_assoc] at hq
  rcases hq with hq|hq|hq|hq|hq|hq|hq
  · exact sign hq
  · exact norm hq
  · exact view hq
  · rw [cmp] at hq
    simp only [Layout.wires,Layout.r,Layout.low,Layout.y,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,Option.toList_none,List.nil_append] at hq ⊢; tauto
  · exact view hq
  · exact un hq
  · exact sign hq

end BalancedCleanup

namespace BalancedCircuit

theorem foldSources (L : Layout) (q : Wire) (hq : q∈mappedWires (foldBits L)) :
    q=L.plus ∨ q=L.minus := by
  obtain ⟨b,hb,hm⟩ := List.mem_flatMap.mp hq
  rw [foldBits] at hb
  rcases List.mem_append.mp hb with hb|hb
  · obtain ⟨i,hi,he⟩ := List.mem_map.mp hb
    subst b
    cases ht : sparseF.testBit (i+1)
    · right; simpa [ht] using hm
    · left; simpa [ht] using hm
  · have he : b={wire:=none,flip:=false} := by simpa using hb
    subst b
    simp at hm

theorem support (L : Layout) (hw : L.Widths) :
    wires (program L) ⊆ L.wires.toFinset := by
  have w := widths L hw
  have cleanup := BalancedCleanup.support L.toLayout hw
  have add := addInPlace_wires (rawSource L) (rawTarget L) L.carry L.sign
    (by omega) (by omega)
  have comp := signComplement_wires_subset L.sign (rawSource L)
  have mapped := mappedAdd_wires_subset (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity
  have rot := (rotate_wires (rawTarget L)).1
  have member (q : Wire) : q∈L.wires.toFinset ↔
      q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0] ∨
      q∈L.rtail ∨ q∈L.ylow ∨ q∈L.carry := by
    simp [Layout.wires,BalancedCleanup.Layout.wires,or_assoc]
  have raw : wires (rawAdd L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [rawAdd,wires_append,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq|hq
    · have h := comp hq
      simp only [member,rawSource,BalancedCleanup.Layout.y,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
    · rw [add] at hq
      simp only [member,rawSource,rawTarget,BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
    · have h := comp hq
      simp only [member,rawSource,BalancedCleanup.Layout.y,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
  have foldSupport : wires (fold L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [fold,wires_append,Finset.mem_union] at hq
    rcases hq with hq|hq
    · have h := mapped hq
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
        foldTarget,or_false,or_assoc] at h
      rcases h with h|h|h|h|h|h|h
      · rcases foldSources L q h with e|e
        all_goals exact (member q).mpr (Or.inl (by simp [e]))
      · exact (member q).mpr (Or.inr (Or.inl h))
      · exact (member q).mpr (Or.inl (by simp [h]))
      · exact (member q).mpr (Or.inl (by simp [h]))
      · exact (member q).mpr (Or.inl (by simp [h]))
      · exact (member q).mpr (Or.inr (Or.inr (Or.inr h)))
      · exact (member q).mpr (Or.inl (by simp [h]))
    · simp only [member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  have seedSmall : wires (seedViews L) ⊆
      [L.ymsb,L.sourceGuard,L.rmsb,L.one,L.ylow.getD 0 0,L.parity,L.r0].toFinset := by
    intro q hq
    simp only [seedViews,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,List.mem_cons,List.not_mem_nil] at hq ⊢
    tauto
  have seed : wires (seedViews L) ⊆ L.wires.toFinset := by
    intro q hq
    have low : L.ylow.getD 0 0∈L.ylow := by
      cases hy : L.ylow with
      | nil => have hh := hw.2.1; simp [hy] at hh
      | cons a as => simp [hy]
    have small := seedSmall hq
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil] at small
    rcases small with e|e|e|e|e|e|e|e
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inr (Or.inr (Or.inl (by simpa [e] using low))))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact (member q).mpr (Or.inl (by simp [e]))
    · exact False.elim e
  intro q hq
  simp only [program,wires_append,Finset.mem_union,or_assoc] at hq
  rcases hq with hq|hq|hq|hq|hq|hq|hq|hq
  · exact seed hq
  · exact raw hq
  · simp only [prepareFold,member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · exact foldSupport hq
  · rw [rot,if_neg (by omega)] at hq
    simp only [member,rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · simp only [releaseSelectors,member,wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · have h := cleanup hq
    simp only [Layout.wires,List.mem_toFinset,List.mem_append] at ⊢
    exact Or.inr (List.mem_toFinset.mp h)
  · simp only [member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto

/-- Distinct gate-support ceiling, not a claim of minimum peak-live width. -/
theorem qubitBound (L : Layout) (hw : L.Widths) : qubitCount (program L)≤776 := by
  have h := Finset.card_le_card (support L hw)
  have n := List.toFinset_card_le L.wires
  rw [declaredSites L hw] at n
  exact h.trans n

end BalancedCircuit
end ECDSAAdd.Arithmetic

#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.support
#print axioms ECDSAAdd.Arithmetic.BalancedCircuit.support
#print axioms ECDSAAdd.Arithmetic.BalancedCircuit.qubitBound
