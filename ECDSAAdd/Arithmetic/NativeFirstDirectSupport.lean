import ECDSAAdd.Arithmetic.NativeFirstDirectLayout

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] mappedAdd hAdd kAdd lowCopy forward inverse wires

/-- All actual quantum sites, including retained sign and carry-in. -/
def prefixSites (w : Nat → Wire) : List Wire :=
  wireBlock w 0 257 ++ wireBlock w 770 258 ++ wireBlock w 1540 256 ++
    [w 1028,w 1797]

private theorem block_inside (w : Nat → Wire) (a n : Nat)
    (ha : a+n≤257 ∨ (770≤a ∧ a+n≤1028) ∨ (1540≤a ∧ a+n≤1796)) :
    ∀q∈wireBlock w a n,q∈prefixSites w := by
  intro q hq
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  have mem (b m : Nat) (hb : b ≤ i ∧ i < b+m) : q∈wireBlock w b m := by
    apply List.mem_map.mpr
    exact ⟨i,by simpa only [List.mem_range'_1] using hb,he⟩
  simp only [prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases ha with h|h|h
  · exact Or.inl (Or.inl (Or.inl (mem 0 257 (by omega))))
  · exact Or.inl (Or.inl (Or.inr (mem 770 258 (by omega))))
  · exact Or.inl (Or.inr (mem 1540 256 (by omega)))

private theorem scalar_inside (w : Nat → Wire) (i : Nat)
    (hi : i=0 ∨ i=770 ∨ i=1028 ∨ i=1797) : w i∈prefixSites w := by
  rcases hi with rfl|rfl|rfl|rfl
  · exact block_inside w 0 257 (by omega) _ (by simp [wireBlock,List.range'])
  · exact block_inside w 770 258 (by omega) _ (by simp [wireBlock,List.range'])
  · simp [prefixSites]
  · simp [prefixSites]

private theorem h_support (w : Nat → Wire) (inv : Bool) :
    wires (hAdd w inv) ⊆ (prefixSites w).toFinset := by
  rw [hAdd]
  apply Finset.Subset.trans (mappedAdd_wires_subset (hBits w inv)
    (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797))
  intro q hq
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
  rcases hq with ((hq|hq)|hq)|hq
  · rw [hBits_wire w inv q hq]
    exact scalar_inside w 1028 (by omega)
  · exact block_inside w 4 253 (by omega) q hq
  · exact block_inside w 1540 252 (by omega) q hq
  · subst q; exact scalar_inside w 1797 (by omega)

private theorem k_support (w : Nat → Wire) (inv : Bool) :
    wires (kAdd w inv) ⊆ (prefixSites w).toFinset := by
  intro q hq
  simp only [kAdd,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · have h := mappedAdd_wires_subset (kBits w inv) (wireBlock w 771 257)
      (wireBlock w 1540 256) (w 770) hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    apply List.mem_toFinset.mpr
    rcases h with ((h|h)|h)|h
    · rw [kBits_wire w inv q h]; exact scalar_inside w 1028 (by omega)
    · exact block_inside w 771 257 (by omega) q h
    · exact block_inside w 1540 256 (by omega) q h
    · subst q; exact scalar_inside w 770 (by omega)
  · have eq : q=w 770 := by simpa [wires,Instr.wires] using hq
    subst q; exact List.mem_toFinset.mpr (scalar_inside w 770 (by omega))

private theorem copy_support (w : Nat → Wire) :
    wires (lowCopy w) ⊆ (prefixSites w).toFinset := by
  have hn : wireBlock w 771 255 ≠ [] := by
    intro h
    have hl := wireBlock_length w 771 255
    rw [h] at hl
    simp at hl
  rw [lowCopy,copyRegister_wires none _ _ (by simp [wireBlock_length])]
  simp only [List.isEmpty_iff,hn,if_false,Option.toList_none,List.nil_append]
  intro q hq
  simp only [List.mem_toFinset,List.mem_append] at hq
  apply List.mem_toFinset.mpr
  rcases hq with hq|hq
  · exact block_inside w 771 255 (by omega) q hq
  · exact block_inside w 1 255 (by omega) q hq

theorem prefix_support (w : Nat → Wire) :
    wires (forward w) ⊆ (prefixSites w).toFinset ∧
    wires (inverse w) ⊆ (prefixSites w).toFinset := by
  have hr := rotate_wires (wireBlock w 770 258)
  simp only [wireBlock_length,show ¬(258<2) by omega,if_false] at hr
  have rR : wires (rotateRight (wireBlock w 770 258)) ⊆ (prefixSites w).toFinset := by
    intro q hq
    rw [hr.1] at hq
    exact List.mem_toFinset.mpr (block_inside w 770 258 (by omega) q (List.mem_toFinset.mp hq))
  have rL : wires (rotateLeft (wireBlock w 770 258)) ⊆ (prefixSites w).toFinset := by
    intro q hq
    rw [hr.2] at hq
    exact List.mem_toFinset.mpr (block_inside w 770 258 (by omega) q (List.mem_toFinset.mp hq))
  have h0 := List.mem_toFinset.mpr (scalar_inside w 0 (by omega))
  have hB := List.mem_toFinset.mpr (scalar_inside w 770 (by omega))
  have hS := List.mem_toFinset.mpr (scalar_inside w 1028 (by omega))
  constructor <;> intro q hq
  · simp only [forward,wires_append,Finset.mem_union] at hq
    rcases hq with ((((hq|hq)|hq)|hq)|hq)|hq
    · simp [wires,Instr.wires] at hq
      rcases hq with rfl|rfl|rfl <;> assumption
    · exact copy_support w hq
    · exact h_support w false hq
    · simp [wires,Instr.wires] at hq
      rcases hq with rfl|rfl <;> assumption
    · exact rR hq
    · exact k_support w false hq
  · simp only [inverse,wires_append,Finset.mem_union] at hq
    rcases hq with ((((hq|hq)|hq)|hq)|hq)|hq
    · exact k_support w true hq
    · exact rL hq
    · simp [wires,Instr.wires] at hq
      rcases hq with rfl|rfl <;> assumption
    · exact h_support w true hq
    · exact copy_support w hq
    · simp [wires,Instr.wires] at hq
      rcases hq with rfl|rfl|rfl <;> assumption

theorem prefix_qubitBound (w : Nat → Wire) :
    qubitCount (forward w)≤773 ∧ qubitCount (inverse w)≤773 := by
  have h := prefix_support w
  have hc := List.toFinset_card_le (prefixSites w)
  have hl : (prefixSites w).length=773 := by simp [prefixSites,wireBlock_length]
  rw [hl] at hc
  exact ⟨(Finset.card_le_card h.1).trans hc,(Finset.card_le_card h.2).trans hc⟩

theorem prefix_pool_subset (w : Nat → Wire) :
    prefixSites w ⊆ skywalkPoolWires w := by
  intro q hq
  simp only [prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
  rcases hq with ((hq|hq)|hq)|(hq|hq)
  all_goals first
    | obtain ⟨i,hi,he⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact ⟨i,by omega,he⟩
    | subst q; exact ⟨1028,by omega,rfl⟩
    | subst q; exact ⟨1797,by omega,rfl⟩

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.prefix_support
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.prefix_qubitBound
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.prefix_pool_subset
