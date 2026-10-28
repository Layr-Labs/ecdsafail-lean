import ECDSAAdd.Arithmetic.SkywalkShared

namespace ECDSAAdd.Arithmetic

/-- Full signed words, shared carry frame and threshold workspace for the
exact fused kernel. The retired integer transcript is excluded. -/
def fusedSharedIds : List Nat :=
  1797::(List.range' 770 258++(List.range' 2056 257++[769])++
    (List.range' 1540 257++[2055])++(List.range' 1798 257++[2313])++List.range' 512 256)

private theorem fused_append_region (xs : List Nat) (hn : xs.Nodup) (s n : Nat)
    (hsep : ∀ i∈xs,i < s ∨ s+n ≤ i) : (xs++List.range' s n).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨hn,List.nodup_range',?_⟩
  apply List.disjoint_left.mpr
  intro i hi hj
  have hs := hsep i hi
  simp only [List.mem_range'_1] at hj
  omega

theorem fusedSharedIds_nodup : fusedSharedIds.Nodup := by
  have h1 := fused_append_region (List.range' 770 258) List.nodup_range' 2056 257 (by
    intro i hi; simp only [List.mem_range'_1] at hi; omega)
  have h2 := fused_append_region _ h1 1540 257 (by
    intro i hi; simp only [List.mem_append,List.mem_range'_1] at hi; omega)
  have h3 := fused_append_region _ h2 1798 257 (by
    intro i hi; simp only [List.mem_append,List.mem_range'_1] at hi; omega)
  have h4 := fused_append_region _ h3 512 256 (by
    intro i hi; simp only [List.mem_append,List.mem_range'_1] at hi; omega)
  have h5 : (769::2055::2313::1797::(List.range' 770 258++List.range' 2056 257++
      List.range' 1540 257++List.range' 1798 257++List.range' 512 256)).Nodup := by
    rw [List.nodup_cons,List.nodup_cons,List.nodup_cons,List.nodup_cons]
    refine ⟨?_,?_,?_,?_,h4⟩
    all_goals
      simp only [List.mem_cons,List.mem_append,List.mem_range'_1]
      omega
  apply List.nodup_iff_count.mpr
  intro i
  have hc := List.nodup_iff_count.mp h5 i
  simp only [fusedSharedIds,List.count_cons,List.count_append,List.count_nil] at hc ⊢
  omega

theorem fusedSharedIds_bound (i : Nat) (hi : i∈fusedSharedIds) : i < 2314 := by
  simp only [fusedSharedIds,List.mem_cons,List.mem_append,List.mem_range'_1,
    List.not_mem_nil,or_false] at hi
  omega

/-- The sign record remains outside the borrowed sites. It can be a live
transcript bit inside the shared universe; no extra allocation is hidden. -/
theorem fusedSharedSites_nodup (w : Nat → Wire) (b : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hb : b∉fusedSharedIds.map w) :
    (b::fusedSharedIds.map w).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · exact hb
  · apply List.Nodup.map_on
    · intro i hi j hj he
      exact skywalkShared_index_inj w hn i j (fusedSharedIds_bound i hi)
        (fusedSharedIds_bound j hj) he
    · exact fusedSharedIds_nodup

theorem fusedSharedSites_subset (w : Nat → Wire) :
    fusedSharedIds.map w ⊆ skywalkSharedWires w := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  apply List.mem_map.mpr
  exact ⟨i,by simp only [List.mem_range'_1]; exact ⟨Nat.zero_le i,fusedSharedIds_bound i hi⟩,rfl⟩

/-- Both actual controls of each recorded field cell are disjoint from the
fused workspace, even though the controls belong to the same shared pool. -/
theorem fusedSharedSites_record_outside (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (i : Nat) (hi : i < 512) :
    w i∉fusedSharedIds.map w ∧ w (1028+i)∉fusedSharedIds.map w := by
  have away (j : Nat) (hj : j < 2314) (hnot : j∉fusedSharedIds) :
      w j∉fusedSharedIds.map w := by
    intro hm
    obtain ⟨k,hk,he⟩ := List.mem_map.mp hm
    have eq := skywalkShared_index_inj w hn k j (fusedSharedIds_bound k hk) hj he
    exact hnot (eq ▸ hk)
  constructor
  · apply away i (by omega)
    simp only [fusedSharedIds,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false]
    omega
  · apply away (1028+i) (by omega)
    simp only [fusedSharedIds,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false]
    omega

end ECDSAAdd.Arithmetic
