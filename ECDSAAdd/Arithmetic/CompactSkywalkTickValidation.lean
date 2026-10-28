import ECDSAAdd.Arithmetic.CompactSkywalkTickLayout

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private def compactTickControls (i : Nat) : List Nat :=
  [skywalkPoolPreviousId i,1028+i,i+compactSkywalkTickPreWidth i,i,770]
private def compactTickBlocks (i : Nat) : List Nat :=
  List.range' (i+1) (compactSkywalkTickPreWidth i-1)++
    List.range' 771 (compactSkywalkTickPreWidth i-1)++
    List.range' 1540 (compactSkywalkTickPreWidth i-1)
private def compactTickIds (i : Nat) : List Nat := compactTickControls i++compactTickBlocks i

private theorem compactTickIdsND (i : Nat) (hi : i < 512) : (compactTickIds i).Nodup := by
  have hn := compactSkywalkTick_width_bounds i hi
  have a : (List.range' (i+1) (compactSkywalkTickPreWidth i-1)++
      List.range' 771 (compactSkywalkTickPreWidth i-1)).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨List.nodup_range',List.nodup_range',?_⟩
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_range'_1] at hj hk
    omega
  have b : (compactTickBlocks i).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨a,List.nodup_range',?_⟩
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_append,List.mem_range'_1] at hj hk
    omega
  have c : (compactTickControls i).Nodup := by
    by_cases hz : i = 0
    · subst i
      norm_num [compactTickControls,skywalkPoolPreviousId,compactSkywalkTickPreWidth,
        narrowSkywalkRouteWidth]
    · simp [compactTickControls,skywalkPoolPreviousId,hz]
      omega
  apply List.nodup_append'.mpr
  refine ⟨c,b,?_⟩
  apply List.disjoint_left.mpr
  intro j hj hk
  simp only [compactTickControls,List.mem_cons,List.not_mem_nil,or_false] at hj
  simp only [compactTickBlocks,List.mem_append,List.mem_range'_1] at hk
  by_cases hz : i = 0
  · simp only [skywalkPoolPreviousId,if_pos hz] at hj
    omega
  · simp only [skywalkPoolPreviousId,if_neg hz] at hj
    omega

private theorem compactTickIdsBound (i j : Nat) (hi : i < 512)
    (hj : j ∈ compactTickIds i) : j < 1798 := by
  have hn := compactSkywalkTick_width_bounds i hi
  simp only [compactTickIds,compactTickControls,compactTickBlocks,List.mem_append,
    List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
  by_cases hz : i = 0
  · simp only [skywalkPoolPreviousId,if_pos hz] at hj
    omega
  · simp only [skywalkPoolPreviousId,if_neg hz] at hj
    omega

private theorem compactTickWires (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).wires = (compactTickIds i).map w := by
  change w (skywalkPoolPreviousId i)::w (1028+i)::w (i+compactSkywalkTickPreWidth i)::
    w i::w 770::((compactSkywalkTickLayout w i).ah++(compactSkywalkTickLayout w i).bh++
      wireBlock w 1540 (compactSkywalkTickPreWidth i-1)) = _
  rw [compactSkywalkTick_ah w i hi,compactSkywalkTick_bh w i hi]
  simp [compactTickIds,compactTickControls,compactTickBlocks,wireBlock,List.map_append]

/-- The actual variable-width local tick has no aliases under pool injectivity. -/
theorem compactSkywalkTick_valid (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) : (compactSkywalkTickLayout w i).Valid := by
  constructor
  · simp [compactSkywalkTickLayout,wireBlock]
  · rw [compactSkywalkTick_ah w i hi]
    simp [compactSkywalkTickLayout,wireBlock]
  · rw [compactTickWires w i hi]
    apply List.Nodup.map_on
    · intro a ha b hb he
      exact skywalkPool_index_inj w hn a b (compactTickIdsBound i a hi ha)
        (compactTickIdsBound i b hi hb) he
    · exact compactTickIdsND i hi

theorem compactSkywalkTick_local_support (w : Nat → Wire) (i : Nat) (hi : i < 512) :
    (compactSkywalkTickLayout w i).wires ⊆ skywalkPoolWires w := by
  rw [compactTickWires w i hi]
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  simp only [skywalkPoolWires,wireBlock,List.mem_map,List.mem_range'_1]
  exact ⟨j,by have h := compactTickIdsBound i j hi hj; omega,rfl⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkTick_valid
