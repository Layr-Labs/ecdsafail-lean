import ECDSAAdd.Arithmetic.NativeFirstDirectProgram
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect

theorem index_ne (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i j : Nat) (hi : i<1798) (hj : j<1798) (hne : i≠j) : w i≠w j := by
  intro h
  exact hne (skywalkPool_index_inj w hn i j hi hj h)

theorem block_not_mem (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i a n : Nat) (hi : i<1798) (ha : a+n≤1798)
    (sep : i < a ∨ a + n ≤ i) : w i ∉ wireBlock w a n := by
  intro h
  obtain ⟨j,hj,he⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hj
  have eq := skywalkPool_index_inj w hn i j hi (by omega) he.symm
  omega

theorem block_nodup (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (a n : Nat) (ha : a+n≤1798) : (wireBlock w a n).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj he
    simp only [List.mem_range'_1] at hi hj
    exact skywalkPool_index_inj w hn i j (by omega) (by omega) he
  · exact List.nodup_range'

theorem block_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (a n b m : Nat) (ha : a+n≤1798) (hb : b+m≤1798)
    (sep : a+n≤b ∨ b+m≤a) :
    List.Disjoint (wireBlock w a n) (wireBlock w b m) := by
  apply List.disjoint_left.mpr
  intro q hq hk
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hq
  obtain ⟨j,hj,hf⟩ := List.mem_map.mp hk
  simp only [List.mem_range'_1] at hi hj
  have eq := skywalkPool_index_inj w hn i j (by omega) (by omega) (he.trans hf.symm)
  omega

theorem block_subset (w : Nat → Wire) (a n m : Nat) (h : n≤m) :
    ∀q∈wireBlock w a n,q∈wireBlock w a m := by
  intro q hq
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hq
  apply List.mem_map.mpr
  refine ⟨i,?_,he⟩
  simp only [List.mem_range'_1] at hi ⊢
  omega

private theorem two_ranges_nd (a n b m : Nat) (sep : a+n≤b) :
    (List.range' a n++List.range' b m).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨List.nodup_range',List.nodup_range',?_⟩
  apply List.disjoint_left.mpr
  intro q hq hk
  simp only [List.mem_range'_1] at hq hk
  omega

private theorem map_pool_nd (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (ids : List Nat) (hi : ∀i∈ids,i<1798) (hd : ids.Nodup) : (ids.map w).Nodup := by
  apply List.Nodup.map_on
  · intro i him j hjm he
    exact skywalkPool_index_inj w hn i j (hi i him) (hi j hjm) he
  · exact hd

theorem h_inputs_nd (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    (w 1797::(wireBlock w 4 253++wireBlock w 1540 252)).Nodup := by
  have hd : (1797::(List.range' 4 253++List.range' 1540 252)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,two_ranges_nd 4 253 1540 252 (by omega)⟩
    intro h
    simp only [List.mem_append,List.mem_range'_1] at h
    omega
  have a := map_pool_nd w hn _ (by
    intro i hi
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hi
    omega) hd
  simpa only [List.map_cons,List.map_append,wireBlock] using a

theorem k_inputs_nd (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    (w 770::(wireBlock w 771 257++wireBlock w 1540 256)).Nodup := by
  have hd : (770::(List.range' 771 257++List.range' 1540 256)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,two_ranges_nd 771 257 1540 256 (by omega)⟩
    intro h
    simp only [List.mem_append,List.mem_range'_1] at h
    omega
  have a := map_pool_nd w hn _ (by
    intro i hi
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hi
    omega) hd
  simpa only [List.map_cons,List.map_append,wireBlock] using a

private theorem flag_choice_wire (flag q : Wire) (bit : Bool)
    (hq : q∈(if bit then ({wire:=some flag,flip:=false} : MappedBit)
      else {wire:=none,flip:=false}).wire.toList) : q=flag := by
  cases bit <;> simp_all

theorem hBits_wire (w : Nat → Wire) (inverse : Bool) (q : Wire)
    (hq : q∈mappedWires (hBits w inverse)) : q=w 1028 := by
  obtain ⟨bit,hbit,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨j,_hj,rfl⟩ := List.mem_map.mp hbit
  exact flag_choice_wire (w 1028) q
    ((if inverse then 2^256-hConstant else hConstant).testBit (j+3)) hq

theorem kBits_wire (w : Nat → Wire) (inverse : Bool) (q : Wire)
    (hq : q∈mappedWires (kBits w inverse)) : q=w 1028 := by
  obtain ⟨bit,hbit,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨j,_hj,rfl⟩ := List.mem_map.mp hbit
  dsimp only at hq
  split at hq <;> simp_all

theorem h_sources_fresh (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (inverse : Bool) : ∀q∈mappedWires (hBits w inverse),
      q∉w 1797::(wireBlock w 4 253++wireBlock w 1540 252) := by
  intro q hq
  rw [hBits_wire w inverse q hq]
  simp only [List.mem_cons,List.mem_append,not_or]
  exact ⟨index_ne w hn 1028 1797 (by omega) (by omega) (by omega),
    block_not_mem w hn 1028 4 253 (by omega) (by omega) (by omega),
    block_not_mem w hn 1028 1540 252 (by omega) (by omega) (by omega)⟩

theorem k_sources_fresh (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (inverse : Bool) : ∀q∈mappedWires (kBits w inverse),
      q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256) := by
  intro q hq
  rw [kBits_wire w inverse q hq]
  simp only [List.mem_cons,List.mem_append,not_or]
  exact ⟨index_ne w hn 1028 770 (by omega) (by omega) (by omega),
    block_not_mem w hn 1028 771 257 (by omega) (by omega) (by omega),
    block_not_mem w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩

theorem copy_inputs_nd (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    (wireBlock w 771 255++wireBlock w 1 255).Nodup := by
  exact List.nodup_append'.mpr ⟨block_nodup w hn _ _ (by omega),
    block_nodup w hn _ _ (by omega),block_disjoint w hn _ _ _ _ (by omega) (by omega) (by omega)⟩

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.index_ne
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.block_not_mem
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.block_nodup
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.block_disjoint
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.block_subset
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.h_inputs_nd
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.k_inputs_nd
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.hBits_wire
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.kBits_wire
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.h_sources_fresh
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.k_sources_fresh
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.copy_inputs_nd
