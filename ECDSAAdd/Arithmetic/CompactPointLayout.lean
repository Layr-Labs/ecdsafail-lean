import ECDSAAdd.Arithmetic.SkywalkDirectPointLayout
import ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupportLayout

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.ControlledPointLayout

/-- Actual compact scratch: integer pool, one canonical guard, zero-repair
carry-in, two selectors and original-zero flag. The bank gap is omitted. -/
def compactPointPool (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 0 1542 ++ wireBlock L.core.poolWire 1800 5

def compactPointSites (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ L.inPlaceFlags ++ L.compactPointPool

theorem compactPointSites_length (L : ControlledPointLayout) (hw : L.Widths) :
    L.compactPointSites.length=2068 := by
  simp [compactPointSites,compactPointPool,PointAddLayout.pointWires,inPlaceFlags,
    point,hw.inputX,hw.inputY,wireBlock]

theorem compactPointPool_count (L : ControlledPointLayout) (hw : L.Widths) (q : Wire) :
    L.compactPointPool.count q  ≤  L.dialogPool.count q := by
  have split : wireBlock L.core.poolWire 0 1805 =
      wireBlock L.core.poolWire 0 1542 ++ wireBlock L.core.poolWire 1542 258 ++
      wireBlock L.core.poolWire 1800 5 := by
    rw [←wireBlock_append L.core.poolWire 0 1542 263,
      ←wireBlock_append L.core.poolWire 1542 258 5,List.append_assoc]
  have hp := (List.take_sublist 1805 L.dialogPool).count_le q
  have he : L.dialogPool.take 1805=wireBlock L.core.poolWire 0 1805 := by
    rw [L.core.pool_prefix hw 1805 (by omega)]
    simp [dialogPool,List.take_take]
  rw [he,split] at hp
  simp only [compactPointPool,List.count_append] at hp ⊢
  omega

theorem compactPointSites_nodup (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : L.compactPointSites.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp := L.compactPointPool_count hw q
  simp only [compactPointSites,dialogUsedWires,List.count_append] at h ⊢
  omega

theorem compactPointPool_prefix (L : ControlledPointLayout) (hw : L.Widths)
    (n : Nat) (hn : n ≤ 1542) : L.dialogPool.take n ⊆ L.compactPointPool := by
  have he : L.dialogPool.take 1542=wireBlock L.core.poolWire 0 1542 := by
    rw [L.core.pool_prefix hw 1542 (by omega)]
    simp [dialogPool,List.take_take]
  have ht : (L.dialogPool.take 1542).take n=L.dialogPool.take n := by
    rw [List.take_take,Nat.min_eq_left hn]
  intro q hq
  rw [←ht] at hq
  have hm := List.mem_of_mem_take hq
  rw [he] at hm
  exact List.mem_append_left _ hm

private theorem compact_prefix (pool : Nat → Wire) (x y : List Wire) :
    wireBlock (skywalkPointWire pool x y) 0 770=wireBlock pool 0 770 := by
  simp only [wireBlock,List.range'_eq_map_range,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hb := List.mem_range.mp hi
  simp only [Function.comp_def,Nat.zero_add]
  change skywalkPointWire pool x y i=pool i
  simp [skywalkPointWire,show ¬(770 ≤ i ∧ i < 1026) by omega,
    show ¬(2056 ≤ i ∧ i < 2312) by omega,show ¬1026 ≤ i by omega,show ¬2312 ≤ i by omega]

private theorem compact_middle (pool : Nat → Wire) (x y : List Wire) :
    wireBlock (skywalkPointWire pool x y) 1026 772=wireBlock pool 770 772 := by
  simp only [wireBlock,List.range'_eq_map_range,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hb := List.mem_range.mp hi
  have hid : 1026+i-256=770+i := by omega
  simp [skywalkPointWire,show ¬(2056 ≤ 1026+i ∧ 1026+i < 2312) by omega,
    show 1026 ≤ 1026+i by omega,show ¬2312 ≤ 1026+i by omega,hid]

theorem compactSharedMap_support (L : ControlledPointLayout) (hw : L.Widths) :
    (compactSharedSites L.skywalkDirectMap).toFinset ⊆
      (L.core.generic::L.point.x++L.point.y++L.compactPointPool).toFinset := by
  have hxlen : L.point.x.length=256 := hw.inputX
  have hylen : L.point.y.length=256 := hw.inputY
  have hp : wireBlock L.skywalkDirectMap 0 1798 =
      wireBlock L.core.poolWire 0 770 ++ L.point.x ++ wireBlock L.core.poolWire 770 772 := by
    rw [←wireBlock_append L.skywalkDirectMap 0 770 1028,
      ←wireBlock_append L.skywalkDirectMap 770 256 772]
    simp only [Nat.reduceAdd,skywalkDirectMap]
    rw [compact_prefix,compact_middle,
      skywalkPointWire_x L.core.poolWire L.point.x L.point.y hxlen]
    simp only [List.append_assoc]
  have hy : wireBlock L.skywalkDirectMap 2056 257=L.point.y++[L.core.poolWire 1800] := by
    rw [←wireBlock_append L.skywalkDirectMap 2056 256 1]
    simp only [Nat.reduceAdd,skywalkDirectMap]
    rw [skywalkPointWire_y L.core.poolWire L.point.x L.point.y hylen]
    congr 1
  have whole : wireBlock L.core.poolWire 0 1542=
      wireBlock L.core.poolWire 0 770++wireBlock L.core.poolWire 770 772 :=
    (wireBlock_append L.core.poolWire 0 770 772).symm
  have guard : L.core.poolWire 1800∈wireBlock L.core.poolWire 1800 5 := by
    apply List.mem_map.mpr
    exact ⟨1800,by simp [List.mem_range'_1],rfl⟩
  intro q hq
  have hg : q=L.core.poolWire 1800 → q∈wireBlock L.core.poolWire 1800 5 := by
    intro e
    simpa only [e] using guard
  simp only [compactSharedSites,hp,hy,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,or_assoc] at hq
  simp only [compactPointPool,whole,List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc]
  tauto

end ECDSAAdd.Arithmetic.ControlledPointLayout
#print axioms ECDSAAdd.Arithmetic.ControlledPointLayout.compactPointSites_nodup
#print axioms ECDSAAdd.Arithmetic.ControlledPointLayout.compactSharedMap_support
