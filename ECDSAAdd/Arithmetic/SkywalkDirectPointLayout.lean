import ECDSAAdd.Arithmetic.SkywalkPointLayout
import ECDSAAdd.Arithmetic.MixedTranscriptReplay
import ECDSAAdd.Arithmetic.FusedSharedRetainedSupport

set_option maxRecDepth 4096

namespace ECDSAAdd.Arithmetic.ControlledPointLayout

/-- Direct caller-X divisor port. Two selectors and a retained zero flag
occupy three scalar sites beyond the original 1,802-site shared scratch. -/
def skywalkDirectMap (L : ControlledPointLayout) : Nat → Wire :=
  skywalkPointWire L.core.poolWire L.point.x L.point.y

def skywalkDirectSelectorG (L : ControlledPointLayout) := L.core.poolWire 1802
def skywalkDirectSelectorS (L : ControlledPointLayout) := L.core.poolWire 1803
def skywalkDirectZero (L : ControlledPointLayout) := L.core.poolWire 1804

def skywalkDirectDeclaredSites (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags++L.dialogPool.take 1805

/-- A layout capacity theorem, not a resource theorem for an integrated stage. -/
theorem skywalkDirectDeclaredSites_length (L : ControlledPointLayout) (hw : L.Widths) :
    L.skywalkDirectDeclaredSites.length=2326 := by
  simp [skywalkDirectDeclaredSites,PointAddLayout.pointWires,inPlaceFlags,point,
    hw.inputX,hw.inputY,L.dialogPool_length hw]

theorem skywalkDirectDeclaredSites_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    L.skywalkDirectDeclaredSites.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp := (List.take_sublist 1805 L.dialogPool).count_le q
  simp only [skywalkDirectDeclaredSites,dialogUsedWires,List.count_append,List.count_cons,List.count_nil] at hh ⊢
  omega

theorem skywalkDirectMap_nodup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (skywalkSharedWires L.skywalkDirectMap).Nodup := by
  apply skywalkPointWire_nodup L.core.poolWire L.point.x L.point.y hw.inputX hw.inputY
  rw [L.core.pool_prefix hw 1802 (by omega)]
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp : (L.core.pool.take 1802).count q≤L.dialogPool.count q := by
    have h := (List.take_sublist 1802 L.dialogPool).count_le q
    simpa only [dialogPool,List.take_take,Nat.min_eq_left (show 1802≤2613 by omega)] using h
  simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,List.count_nil] at hh ⊢
  omega

theorem skywalkDirectMap_coordinates (L : ControlledPointLayout) (hw : L.Widths) :
    wireBlock L.skywalkDirectMap 770 256=L.point.x ∧
    wireBlock L.skywalkDirectMap 2056 256=L.point.y :=
  ⟨skywalkPointWire_x L.core.poolWire L.point.x L.point.y hw.inputX,
   skywalkPointWire_y L.core.poolWire L.point.x L.point.y hw.inputY⟩

/-- All three scalar flags and the caller control are outside the direct
shared arithmetic universe. The original X and Y are included exactly once. -/
theorem skywalkDirectScalar_nodup (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    (L.core.generic::L.skywalkDirectSelectorG::L.skywalkDirectSelectorS::
      L.skywalkDirectZero::skywalkSharedWires L.skywalkDirectMap).Nodup := by
  have hp : wireBlock L.core.poolWire 0 1805=
      wireBlock L.core.poolWire 0 1802++
      [L.skywalkDirectSelectorG,L.skywalkDirectSelectorS,L.skywalkDirectZero] := by
    have ht : wireBlock L.core.poolWire 1802 3=
        [L.skywalkDirectSelectorG,L.skywalkDirectSelectorS,L.skywalkDirectZero] := by
      simp [wireBlock,List.range',skywalkDirectSelectorG,skywalkDirectSelectorS,skywalkDirectZero]
    simpa only [Nat.zero_add,Nat.reduceAdd,ht] using
      (wireBlock_append L.core.poolWire 0 1802 3).symm
  have hs := skywalkPointWire_shared L.core.poolWire L.point.x L.point.y hw.inputX hw.inputY
  have hc : wireBlock L.core.poolWire 0 1802=wireBlock L.core.poolWire 0 770++
      wireBlock L.core.poolWire 770 1030++wireBlock L.core.poolWire 1800 2 := by
    symm; rw [wireBlock_append,wireBlock_append]
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hm := (List.take_sublist 1805 L.dialogPool).count_le q
  have he : L.dialogPool.take 1805=wireBlock L.core.poolWire 0 1805 := by
    rw [L.core.pool_prefix hw 1805 (by omega)]
    simp [dialogPool,List.take_take]
  rw [he,hp,hc] at hm
  rw [skywalkDirectMap,hs]
  simp only [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.count_cons,
    List.count_append,List.count_nil] at hh hm ⊢
  omega

theorem skywalkDirectMixed_layout (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : MixedTranscriptReplayLayout L.skywalkDirectMap
      L.core.generic L.skywalkDirectSelectorG L.skywalkDirectSelectorS
      (mixedTranscriptTape L.skywalkDirectMap) := by
  let w := L.skywalkDirectMap
  have hall := L.skywalkDirectScalar_nodup hw hn
  have shared := L.skywalkDirectMap_nodup hw hn
  have outside (q : Wire) (hq : q∈[L.core.generic,L.skywalkDirectSelectorG,
      L.skywalkDirectSelectorS,L.skywalkDirectZero]) : q∉skywalkSharedWires w := by
    have hd := List.nodup_append'.mp (show
      ([L.core.generic,L.skywalkDirectSelectorG,L.skywalkDirectSelectorS,
        L.skywalkDirectZero]++skywalkSharedWires w).Nodup from hall)
    exact fun hs => List.disjoint_left.mp hd.2.2 hq hs
  have unused : skywalkSharedUnused w⊆skywalkSharedWires w := by
    intro q hq
    simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    all_goals
      apply List.mem_map.mpr
      exact ⟨_,by simp [List.mem_range'_1],rfl⟩
  apply mixedTranscriptTape_layout
  intro r hr
  have hc := skywalkShared_tape_layout w shared L.core.generic
    (outside _ (by simp)) r hr
  have pair := (List.nodup_cons.mp hc).2
  have sub : (r.2::r.1::(skywalkSharedField w).wires)⊆skywalkSharedWires w := by
    intro q hq
    rcases List.mem_cons.mp hq with hq|hq
    · subst q; exact (retained_tape_subset_shared w r hr).2
    rcases List.mem_cons.mp hq with hq|hq
    · subst q; exact (retained_tape_subset_shared w r hr).1
    · exact retained_field_subset_shared w hq
  constructor
  · exact shared
  · apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hall q
    have hp := List.nodup_iff_count.mp pair q
    have hle : (r.2::r.1::(skywalkSharedField w).wires).count q≤
        (skywalkSharedWires w).count q := by
      by_cases hm : q∈r.2::r.1::(skywalkSharedField w).wires
      · have hpos := List.count_pos_iff.mpr (sub hm); omega
      · rw [List.count_eq_zero.mpr hm]; omega
    dsimp only [w] at hh hp hle ⊢
    simp only [List.count_cons] at hh hp hle ⊢
    omega
  · exact fun h => outside _ (by simp) (fusedSharedSites_subset w h)
  · exact fun h => outside _ (by simp) (unused h)
  · exact fun h => outside _ (by simp) (unused h)

end ECDSAAdd.Arithmetic.ControlledPointLayout
