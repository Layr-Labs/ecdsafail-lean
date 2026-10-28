import ECDSAAdd.Arithmetic.RecordedRailDeferResources

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailDefer

def allSites (a b bank : List Wire) (cin even odd : Wire) : Finset Wire :=
  (cin::even::odd::(a++b++bank)).toFinset

private theorem chunk_mem (r : List Wire) (j : Nat) (q : Wire) (h : q∈chunk r j) : q∈r :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

private theorem boundary_mem (even odd : Wire) (j : Nat) :
    boundary even odd j∈[even,odd] := by
  unfold boundary
  split <;> simp

private theorem vented_sub (a b bank : List Wire) (cin even odd incoming cout : Wire)
    (j : Nat) (ha : a.length=256) (hb : b.length=256) (hbank : bank.length=31)
    (hj : j<8) (hi : incoming∈[cin,even,odd]) (hc : cout∈[even,odd]) :
    recordedWires (RecordedRailVented.vented (chunk a j) (chunk b j) (some incoming) bank cout)
      ⊆ allSites a b bank cin even odd := by
  have aw := chunk_length32 a ha j hj
  have bw := chunk_length32 b hb j hj
  have aligned : RecordedRailVented.Aligned (chunk a j) (chunk b j) bank := by
    simp [RecordedRailVented.Aligned,aw,bw,hbank]
  have h := RecordedRailVented.support _ _ bank (RecordedRailVented.aligned_shape _ _ _ aligned)
    (some incoming) cout
  intro q hq
  have member := h hq
  simp only [RecordedRailVented.sites,List.mem_toFinset,List.mem_append,
    Option.toList_some,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  simp only [allSites,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil] at ⊢
  simp only [or_assoc] at member
  rcases member with rfl|haq|hbq|hk|rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    tauto
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (chunk_mem a j q haq)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (chunk_mem b j q hbq)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hk)))
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    tauto

theorem segment_support (a b bank : List Wire) (cin even odd : Wire)
    (ha : a.length=256) (hb : b.length=256) (hbank : bank.length=31)
    (j : Nat) (hj : j<8) :
    recordedWires (segment a b bank cin even odd j) ⊆ allSites a b bank cin even odd := by
  by_cases zero : j=0
  · subst j
    simpa only [segment,if_pos] using vented_sub a b bank cin even odd cin even 0 ha hb hbank
      (by decide) (by simp) (by simp)
  · by_cases last : j=7
    · subst j
      have aw := chunk_length32 a ha 7 (by decide)
      have bw := chunk_length32 b hb 7 (by decide)
      have aligned : RecordedRailRipple.Aligned (chunk a 7) (chunk b 7)
          (bank.take ((chunk a 7).length-2)) (List.replicate ((chunk a 7).length-2) none) := by
        simp [RecordedRailRipple.Aligned,aw,bw,hbank]
      have h := RecordedRailRipple.ripple_support _ _ _ _
        (RecordedRailRipple.aligned_shape _ _ _ _ aligned) (some even)
      intro q hq
      simp only [segment,show ¬((7:Nat)=0) from by decide,if_neg,if_pos,if_false,if_true,finish,
        recordedWires_append,Finset.mem_union] at hq
      rcases hq with hq|hq
      · have member := h hq
        simp only [RecordedRailRipple.sites,List.mem_toFinset,Option.toList_some,
          List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
        simp only [or_assoc] at member
        have hm : q=even ∨ q∈a ∨ q∈b ∨ q∈bank := by
          rcases member with rfl|haq|hbq|hk
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (chunk_mem a 7 q haq))
          · exact Or.inr (Or.inr (Or.inl (chunk_mem b 7 q hbq)))
          · exact Or.inr (Or.inr (Or.inr (List.mem_of_mem_take hk)))
        simp [allSites,hm] at ⊢
        tauto
      · have eq : q=even := by
          simpa [bareMX,recordedWires,RecordedInstr.quantumWires,Instr.wires,correctionWires] using hq
        subst q
        simp [allSites]
    · have h := vented_sub a b bank cin even odd
        (boundary even odd (j-1)) (boundary even odd j) j ha hb hbank hj
        (by have h := boundary_mem even odd (j-1); simp at h ⊢; tauto)
        (boundary_mem even odd j)
      simp only [segment,zero,last,if_neg,if_false,if_true,advance,recordedWires_append,Finset.union_subset_iff]
      refine ⟨h,?_⟩
      have boundary := boundary_mem even odd (j-1)
      intro q hq
      simp only [bareMX,recordedWires,RecordedInstr.quantumWires,Instr.wires,
        correctionWires,Finset.union_empty,Finset.mem_singleton] at hq
      subst q
      simp [allSites] at ⊢
      simp only [List.mem_cons,List.not_mem_nil,or_false] at boundary
      tauto

theorem forward32_support (a b bank : List Wire) (cin even odd : Wire)
    (ha : a.length=256) (hb : b.length=256) (hbank : bank.length=31) :
    recordedWires (forward32 a b bank cin even odd) ⊆ allSites a b bank cin even odd := by
  simp only [forward32,recordedWires_append,Finset.union_subset_iff]
  repeat constructor
  all_goals exact segment_support a b bank cin even odd ha hb hbank _ (by decide)

theorem forward32_site_bound (a b bank : List Wire) (cin even odd : Wire)
    (ha : a.length=256) (hb : b.length=256) (hbank : bank.length=31) :
    (recordedWires (forward32 a b bank cin even odd)).card ≤546 := by
  have h := Finset.card_le_card (forward32_support a b bank cin even odd ha hb hbank)
  have bound := List.toFinset_card_le (cin::even::odd::(a++b++bank))
  simp only [allSites] at h
  simp only [List.length_cons,List.length_append,ha,hb,hbank] at bound
  omega

end ECDSAAdd.Arithmetic.RecordedRailDefer
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.forward32_support
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.forward32_site_bound
