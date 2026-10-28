import ECDSAAdd.Arithmetic.BalancedSharedPorts
import ECDSAAdd.Arithmetic.BalancedTranscriptBoundary

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Boundary conversion borrows the first 255 restored carry sites. -/
def balancedSharedTargetConvert (w : Nat → Wire) : BalancedConvert.Layout :=
  { low:=wireBlock w 2056 255,msb:=w 2311,carry:=wireBlock w 1540 255,
    cin:=w 1797,one:=w 1027,flag:=w 1796 }

def balancedSharedSourceConvert (w : Nat → Wire) : BalancedConvert.Layout :=
  { low:=wireBlock w 770 255,msb:=w 1025,carry:=wireBlock w 1540 255,
    cin:=w 1797,one:=w 1027,flag:=w 1796 }

/-- Map a finite allocation within the original shared bank. -/
theorem balancedSharedLayout_mapND (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (ids : List Nat)
    (hd : ids.Nodup) (hb : ∀j∈ids,j<2314) : (ids.map w).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj he
    exact skywalkShared_index_inj w hn i j (hb i hi) (hb j hj) he
  · exact hd

/-- Every ID allocation in the shared bank is a subset of that bank. -/
theorem balancedSharedLayout_mapSubset (w : Nat → Wire) (ids : List Nat)
    (hb : ∀j∈ids,j<2314) : ids.map w ⊆ skywalkSharedWires w := by
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  simp only [skywalkSharedWires,wireBlock,List.mem_map,List.mem_range'_1]
  exact ⟨j,by have h := hb j hj; omega,rfl⟩

private def targetIds : List Nat :=
  [1797,1027,1796,2311]++List.range' 2056 255++List.range' 1540 255
private def sourceIds : List Nat :=
  [1797,1027,1796,1025]++List.range' 770 255++List.range' 1540 255
private def pairIds : List Nat := List.range' 2056 256++List.range' 770 256
private def workIds : List Nat := [1796,1797,1027]++List.range' 1540 255
private def kernelWorkIds : List Nat :=
  [765,768,767,766,1796,1797,1027]++List.range' 1540 256

private theorem targetIdsND : targetIds.Nodup := by decide
private theorem sourceIdsND : sourceIds.Nodup := by decide
private theorem workPairIdsND : (workIds++pairIds).Nodup := by decide
private theorem workIds_kernel : workIds ⊆ kernelWorkIds := by decide
private theorem allIds_bound (j : Nat) :
    j∈targetIds ∨ j∈sourceIds ∨ j∈workIds++pairIds → j<2314 := by
  simp only [targetIds,sourceIds,workIds,pairIds,List.mem_append,List.mem_cons,
    List.not_mem_nil,List.mem_range'_1,or_false]
  omega

private theorem targetWires (w : Nat → Wire) :
    (balancedSharedTargetConvert w).wires=targetIds.map w := by
  simp [balancedSharedTargetConvert,BalancedConvert.Layout.wires,targetIds,wireBlock]
private theorem sourceWires (w : Nat → Wire) :
    (balancedSharedSourceConvert w).wires=sourceIds.map w := by
  simp [balancedSharedSourceConvert,BalancedConvert.Layout.wires,sourceIds,wireBlock]
private theorem convertWork (w : Nat → Wire) :
    BalancedConvert.work (balancedSharedTargetConvert w)=workIds.map w ∧
    BalancedConvert.work (balancedSharedSourceConvert w)=workIds.map w := by
  simp [balancedSharedTargetConvert,balancedSharedSourceConvert,BalancedConvert.work,
    BalancedConvert.scratch,workIds,wireBlock]
private theorem pairWires (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y=pairIds.map w := by
  rw [balancedSharedPorts_r,balancedSharedPorts_y]
  simp [pairIds,wireBlock]

theorem balancedSharedTargetConvert_widths (w : Nat → Wire) :
    (balancedSharedTargetConvert w).Widths := by
  simp [BalancedConvert.Layout.Widths,balancedSharedTargetConvert,wireBlock]
theorem balancedSharedSourceConvert_widths (w : Nat → Wire) :
    (balancedSharedSourceConvert w).Widths := by
  simp [BalancedConvert.Layout.Widths,balancedSharedSourceConvert,wireBlock]

theorem balancedSharedTargetConvert_word (w : Nat → Wire) (sign : Wire) :
    (balancedSharedTargetConvert w).word=(balancedSharedPorts w sign).r := by
  rw [balancedSharedPorts_r]
  have h := wireBlock_append w 2056 255 1
  have one : wireBlock w 2311 1=[w 2311] := by simp [wireBlock,List.range']
  change wireBlock w 2056 255++[w 2311]=wireBlock w 2056 256
  simpa only [Nat.reduceAdd,one] using h

theorem balancedSharedSourceConvert_word (w : Nat → Wire) (sign : Wire) :
    (balancedSharedSourceConvert w).word=(balancedSharedPorts w sign).y := rfl

theorem balancedSharedTargetConvert_nodup (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    (balancedSharedTargetConvert w).wires.Nodup := by
  rw [targetWires]
  exact balancedSharedLayout_mapND w hn targetIds targetIdsND
    (fun j hj => allIds_bound j (Or.inl hj))
theorem balancedSharedSourceConvert_nodup (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    (balancedSharedSourceConvert w).wires.Nodup := by
  rw [sourceWires]
  exact balancedSharedLayout_mapND w hn sourceIds sourceIdsND
    (fun j hj => allIds_bound j (Or.inr (Or.inl hj)))

theorem balancedSharedLayout_pairND (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    ((balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup := by
  have h := balancedSharedLayout_mapND w hn (workIds++pairIds) workPairIdsND
    (fun j hj => allIds_bound j (Or.inr (Or.inr hj)))
  rw [List.map_append] at h
  rw [pairWires]
  exact (List.nodup_append'.mp h).2.1

private theorem workAway (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (q : Wire) (hq : q∈workIds.map w) :
    q∉(balancedSharedPorts w sign).r ∧ q∉(balancedSharedPorts w sign).y := by
  have h := balancedSharedLayout_mapND w hn (workIds++pairIds) workPairIdsND
    (fun j hj => allIds_bound j (Or.inr (Or.inr hj)))
  rw [List.map_append] at h
  have dis := List.disjoint_left.mp (List.nodup_append'.mp h).2.2 hq
  rw [←pairWires w sign] at dis
  exact ⟨fun hr => dis (List.mem_append_left _ hr),
    fun hy => dis (List.mem_append_right _ hy)⟩

/-- Concrete entry and exit converters require no additional physical sites. -/
def balancedSharedBoundary (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    BalancedTranscriptBoundary (balancedSharedPorts w sign) where
  target := balancedSharedTargetConvert w
  source := balancedSharedSourceConvert w
  targetWord := balancedSharedTargetConvert_word w sign
  sourceWord := balancedSharedSourceConvert_word w sign
  targetWidths := balancedSharedTargetConvert_widths w
  sourceWidths := balancedSharedSourceConvert_widths w
  targetND := balancedSharedTargetConvert_nodup w hn
  sourceND := balancedSharedSourceConvert_nodup w hn
  pairND := balancedSharedLayout_pairND w sign hn
  targetWorkAway := by
    intro q hq
    rw [(convertWork w).1] at hq
    exact workAway w sign hn q hq
  sourceWorkAway := by
    intro q hq
    rw [(convertWork w).2] at hq
    exact workAway w sign hn q hq

theorem balancedSharedBoundary_work_subset (w : Nat → Wire) (sign : Wire) :
    BalancedConvert.work (balancedSharedTargetConvert w) ⊆
      BalancedCircuit.work (balancedSharedPorts w sign) ∧
    BalancedConvert.work (balancedSharedSourceConvert w) ⊆
      BalancedCircuit.work (balancedSharedPorts w sign) := by
  have hk : BalancedCircuit.work (balancedSharedPorts w sign)=kernelWorkIds.map w := by
    simp [BalancedCircuit.work,balancedSharedPorts,kernelWorkIds,wireBlock]
  rw [(convertWork w).1,(convertWork w).2,hk]
  have hs : workIds.map w ⊆ kernelWorkIds.map w := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    exact List.mem_map.mpr ⟨j,workIds_kernel hj,rfl⟩
  exact ⟨hs,hs⟩

theorem balancedSharedBoundary_clean (w : Nat → Wire) (sign : Wire) (base : BasisState)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) :
    (∀q∈BalancedConvert.work (balancedSharedTargetConvert w),base q=false) ∧
    (∀q∈BalancedConvert.work (balancedSharedSourceConvert w),base q=false) := by
  have hc := balancedSharedPorts_clean w sign base hw hu
  have hs := balancedSharedBoundary_work_subset w sign
  exact ⟨fun q hq => hc q (hs.1 hq),fun q hq => hc q (hs.2 hq)⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.balancedSharedBoundary
#print axioms ECDSAAdd.Arithmetic.balancedSharedBoundary_clean
