import ECDSAAdd.Arithmetic.BalancedInverseComposeProof
import ECDSAAdd.Arithmetic.BalancedTranscriptSupport
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit
theorem support (L : Layout) (hw : L.Widths) :
    wires (program L) ⊆ L.wires.toFinset := by
  have w := widths L hw
  have cleanup : wires (recoverParity L) ⊆ L.toLayout.wires.toFinset := BalancedCleanup.support L.toLayout hw
  have add := subInPlace_wires (rawSource L) (rawTarget L) L.carry L.sign
    (by omega) (by omega)
  have comp := signComplement_wires_subset L.sign (rawSource L)
  have mapped := mappedSub_wires_subset (foldBits L) (foldTarget L++[L.cout]) L.carry L.parity
  have rot := (rotate_wires (rawTarget L)).2
  have member (q : Wire) : q∈L.wires.toFinset ↔
      q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0] ∨
      q∈L.rtail ∨ q∈L.ylow ∨ q∈L.carry := by
    simp [Layout.wires,BalancedCleanup.Layout.wires,or_assoc]
  have raw : wires (rawSubtract L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [rawSubtract,wires_append,Finset.mem_union,or_assoc] at hq
    rcases hq with hq|hq|hq
    · have h := comp hq
      simp only [member,rawSource,BalancedCleanup.Layout.y,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
    · rw [add] at hq
      simp only [member,rawSource,rawTarget,BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
    · have h := comp hq
      simp only [member,rawSource,BalancedCleanup.Layout.y,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto
  have foldSupport : wires (undoFold L) ⊆ L.wires.toFinset := by
    intro q hq
    simp only [undoFold,wires_append,Finset.mem_union] at hq
    rcases hq with hq|hq
    · simp only [member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
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
      | cons a as => simp
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
  · simp only [member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · have h := cleanup hq
    simp only [BalancedCircuit.Layout.wires,List.mem_toFinset,List.mem_append] at ⊢
    exact Or.inr (List.mem_toFinset.mp h)
  · simp only [recoverSelectors,member,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · rw [rot,if_neg (by omega)] at hq
    simp only [member,rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · exact foldSupport hq
  · simp only [undoPreparation,member,wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_cons,List.not_mem_nil] at hq ⊢; tauto
  · exact raw hq
  · rw [wires_reverse] at hq
    exact seed hq
/-- Distinct gate support ceiling for the kernel's emitted instructions. -/
theorem qubitBound (L : Layout) (hw : L.Widths) : qubitCount (program L)≤776 := by
  have h := Finset.card_le_card (support L hw)
  have n := List.toFinset_card_le L.wires
  rw [BalancedCircuit.declaredSites L hw] at n
  exact h.trans n
end ECDSAAdd.Arithmetic.BalancedInverse
#print axioms ECDSAAdd.Arithmetic.BalancedInverse.support

#print axioms ECDSAAdd.Arithmetic.BalancedInverse.qubitBound
