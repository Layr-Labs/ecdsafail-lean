import ECDSAAdd.Arithmetic.BalancedSharedLayoutBoundary

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

private def fieldAvailableIds : List Nat :=
  List.range' 770 257++List.range' 2056 256++[2312]++List.range' 1540 257++
    List.range' 1798 256++[1797]++List.range' 512 257++[2313]++[769,1027,2054,2055]
private def portWorkIds : List Nat :=
  [765,768,767,766,1796,1797,1027]++List.range' 1540 256
private theorem ports_fieldIds : balancedSharedIds ⊆ fieldAvailableIds := by decide

/-- Apart from its externally selected sign, the new kernel is wholly
inside the existing field allocation and the explicitly unused sites. -/
theorem balancedSharedLayout_ids_available (w : Nat → Wire) :
    balancedSharedIds.map w ⊆ (skywalkSharedField w).wires++skywalkSharedUnused w := by
  have he : (skywalkSharedField w).wires++skywalkSharedUnused w=fieldAvailableIds.map w := by
    simp [skywalkSharedField,skywalkSharedUnused,ModInPlaceLayout.wires,
      ModInPlaceLayout.z,ModInPlaceLayout.work,ModAddCoreLayout.z,ModAddCoreLayout.work,
      fieldAvailableIds,wireBlock,List.map_append,List.append_assoc]
  rw [he]
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨j,ports_fieldIds hj,rfl⟩

theorem balancedSharedLayout_wires_except_sign (w : Nat → Wire) (sign q : Wire)
    (hq : q∈(balancedSharedPorts w sign).wires) (hs : q≠sign) :
    q∈(skywalkSharedField w).wires++skywalkSharedUnused w := by
  apply balancedSharedLayout_ids_available w
  simp only [balancedSharedPorts,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,balancedSharedIds,wireBlock,List.map_append,
    List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil] at hq ⊢
  tauto

theorem balancedSharedLayout_pair_subset_field (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y ⊆
      (skywalkSharedField w).wires := by
  intro q hq
  rw [balancedSharedPorts_r,balancedSharedPorts_y] at hq
  have ay := wireBlock_append w 770 256 1
  have hy : wireBlock w 770 257=wireBlock w 770 256++wireBlock w 1026 1 := by
    simpa only [Nat.reduceAdd] using ay.symm
  simp only [List.mem_append] at hq
  rcases hq with hq|hq
  · simp only [ModInPlaceLayout.wires,ModInPlaceLayout.z,ModAddCoreLayout.z,
      skywalkSharedField,List.mem_append,List.mem_cons,List.not_mem_nil]
    tauto
  · simp only [ModInPlaceLayout.wires,skywalkSharedField,hy,List.mem_append]
    tauto

theorem balancedSharedLayout_work_subset_shared (w : Nat → Wire) (sign : Wire) :
    BalancedCircuit.work (balancedSharedPorts w sign) ⊆ skywalkSharedWires w := by
  have he : BalancedCircuit.work (balancedSharedPorts w sign)=portWorkIds.map w := by
    simp [BalancedCircuit.work,balancedSharedPorts,portWorkIds,wireBlock]
  rw [he]
  apply balancedSharedLayout_mapSubset
  intro j hj
  simp only [portWorkIds,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hj
  omega

/-- The ordinary mixed layout gives the five distinct controls and keeps
all of them outside the low-word data ports. Only the two selected flags
need the stronger exclusion from the entire original shared bank. -/
theorem balancedSharedTranscriptLayout (w : Nat → Wire) (b g swap effG effS : Wire)
    (hf : MixedTranscriptFieldLayout w b g swap effG effS)
    (hg : effG∉skywalkSharedWires w) (hs : effS∉skywalkSharedWires w) :
    BalancedTranscriptLayout (balancedSharedPorts w effG) b g swap effS := by
  have gIds : effG∉balancedSharedIds.map w := by
    intro hm
    exact hg (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound hm)
  have outside : ∀q∈[b,g,swap,effG,effS],
      q∉(balancedSharedPorts w effG).r ∧ q∉(balancedSharedPorts w effG).y := by
    intro q hq
    have ho := hf.outside q hq
    have hp := balancedSharedLayout_pair_subset_field w effG
    exact ⟨fun hm => ho (hp (List.mem_append_left _ hm)),
      fun hm => ho (hp (List.mem_append_right _ hm))⟩
  refine ⟨balancedSharedPorts_widths w effG,
    balancedSharedPorts_nodup w effG hf.shared gIds,?_,outside,?_,?_⟩
  · apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hf.controls q
    simp only [balancedSharedPorts,List.count_cons,List.count_nil] at h ⊢
    omega
  · exact ⟨fun hm => hg (balancedSharedLayout_work_subset_shared w effG hm),
      fun hm => hs (balancedSharedLayout_work_subset_shared w effG hm)⟩
  · apply List.nodup_cons.mpr
    refine ⟨?_,balancedSharedLayout_pairND w effG hf.shared⟩
    intro hm
    rcases List.mem_append.mp hm with hm|hm
    · exact (outside effS (by simp)).1 hm
    · exact (outside effS (by simp)).2 hm

/-- Direct arithmetic's existing outside-bank condition is sufficient. -/
theorem balancedSharedTranscriptLayout_direct (w : Nat → Wire) (b g swap effG effS : Wire)
    (hf : MixedTranscriptFieldLayout w b g swap effG effS)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) :
    BalancedTranscriptLayout (balancedSharedPorts w effG) b g swap effS :=
  balancedSharedTranscriptLayout w b g swap effG effS hf
    (ho effG (by simp)) (ho effS (by simp))

/-- Lift an exact original mixed transcript allocation to the centered ABI. -/
theorem balancedSharedTranscriptReplayLayout (w : Nat → Wire) (b effG effS : Wire)
    (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b effG effS ls)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) :
    BalancedTranscriptReplayLayout (balancedSharedPorts w effG) b effS ls := by
  intro l hl
  exact balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 effG effS (hf l hl) ho

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.balancedSharedTranscriptLayout
#print axioms ECDSAAdd.Arithmetic.balancedSharedTranscriptReplayLayout
