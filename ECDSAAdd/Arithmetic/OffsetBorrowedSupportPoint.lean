import ECDSAAdd.Arithmetic.CompactPointLayout
import ECDSAAdd.Arithmetic.CompactOffsetCallerSupport

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
open ControlledPointLayout DirectSkywalk
attribute [local irreducible] pointOffsetBorrowedArithmetic compactOffsetCallerArithmetic

/-- Instruction-derived compact support includes both exact zero-repair branches. -/
theorem pointOffsetBorrowedArithmetic_compact_support (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (multiply : Bool) :
    wires (pointOffsetBorrowedArithmetic L multiply) ⊆
      (L.core.generic::L.point.x++L.point.y++L.compactPointPool).toFinset := by
  let W := (L.core.generic::L.point.x++L.point.y++L.compactPointPool).toFinset
  have pool (i : Nat) (hi : i < 1542 ∨ 1800 ≤ i ∧ i < 1805) : L.core.poolWire i∈W := by
    have hm : L.core.poolWire i∈L.compactPointPool := by
      rcases hi with hi|hi
      · apply List.mem_append_left
        exact arith_mem L.core.poolWire 0 1542 i (by omega) hi
      · apply List.mem_append_right
        exact arith_mem L.core.poolWire 1800 5 i hi.1 hi.2
    simp [W,hm]
  have hb : L.core.generic∈W := by simp [W]
  have hg : L.skywalkDirectSelectorG∈W := pool 1802 (Or.inr ⟨by omega,by omega⟩)
  have hs : L.skywalkDirectSelectorS∈W := pool 1803 (Or.inr ⟨by omega,by omega⟩)
  have hz : L.skywalkDirectZero∈W := pool 1804 (Or.inr ⟨by omega,by omega⟩)
  have hi : directSkywalkCin L∈W := pool 1801 (Or.inr ⟨by omega,by omega⟩)
  have kernel := compactOffsetCallerArithmetic_support (!multiply) L.skywalkDirectMap
    (L.skywalkDirectMap_nodup hw hn) L.core.generic L.skywalkDirectSelectorG L.skywalkDirectSelectorS
    W (L.compactSharedMap_support hw) hb hg hs
  have own : (L.skywalkDirectZero::directSkywalkCin L::(L.point.x++directSkywalkCarry L)).toFinset⊆W := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|hx|hc
    · exact hz
    · exact hi
    · simp [W,hx]
    · rw [directSkywalkCarry,wireBlock] at hc
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
      simp only [List.mem_range'_1] at hj
      exact pool j (Or.inl (by omega))
  have repair := (directZeroDivisor_wires L.point.x (directSkywalkCarry L)
    (directSkywalkCin L) L.skywalkDirectZero).trans own
  rw [wires_append] at repair
  have enter : wires (directZeroDivisorEnter L.point.x (directSkywalkCarry L)
      (directSkywalkCin L) L.skywalkDirectZero)⊆W := fun _ h => repair (Finset.mem_union_left _ h)
  have leave : wires (directZeroDivisorLeave L.point.x (directSkywalkCarry L)
      (directSkywalkCin L) L.skywalkDirectZero)⊆W := fun _ h => repair (Finset.mem_union_right _ h)
  simp only [pointOffsetBorrowedArithmetic,directZeroControlled,wires_append,Finset.union_subset_iff]
  exact ⟨enter,kernel,leave⟩

theorem pointOffsetBorrowedArithmetic_compact_declared (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (multiply : Bool) :
    wires (pointOffsetBorrowedArithmetic L multiply)⊆L.compactPointSites.toFinset := by
  apply (pointOffsetBorrowedArithmetic_compact_support L hw hn multiply).trans
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq
  simp only [compactPointSites,PointAddLayout.pointWires,inPlaceFlags,List.mem_toFinset,
    List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc]
  tauto

theorem pointOffsetBorrowedArithmetic_compact_resources (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (multiply : Bool) :
    wires (pointOffsetBorrowedArithmetic L multiply)⊆L.compactPointSites.toFinset ∧
    L.compactPointSites.Nodup ∧ L.compactPointSites.length=2068 ∧
    qubitCount (pointOffsetBorrowedArithmetic L multiply)≤2068 := by
  have sup := pointOffsetBorrowedArithmetic_compact_declared L hw hn multiply
  have nd := L.compactPointSites_nodup hw hn
  have len := L.compactPointSites_length hw
  refine ⟨sup,nd,len,?_⟩
  unfold qubitCount
  calc
    _ ≤ L.compactPointSites.toFinset.card := Finset.card_le_card sup
    _ = 2068 := by rw [List.toFinset_card_of_nodup nd,len]
end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.pointOffsetBorrowedArithmetic_compact_support
#print axioms ECDSAAdd.Arithmetic.pointOffsetBorrowedArithmetic_compact_resources
