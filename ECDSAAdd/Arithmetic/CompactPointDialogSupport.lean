import ECDSAAdd.Arithmetic.PointDialogSupport
import ECDSAAdd.Arithmetic.OffsetBorrowedSupportPoint
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1
attribute [local irreducible] pointOffsetBorrowedArithmetic directSkywalkArithmetic directZeroControlled
  pointRecoveryConstantAdd compactRecoveryConstant pointRecoveryReflection CompactRecoveryNegateLayout.reflection
theorem pointDialogGeneric_compact_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) :
    wires (pointDialogGeneric L cx cy)⊆(L.core.generic::L.point.x++L.point.y++L.compactPointPool).toFinset := by
  let S := (L.core.generic::L.point.x++L.point.y++L.compactPointPool).toFinset
  have prefixSmall (n : Nat) (hn : n≤1542) : L.dialogPool.take n⊆L.compactPointPool :=
    L.compactPointPool_prefix hw n hn
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (pointDialogConstantAdd L r k)⊆S := by
    have sup := pointRecoveryConstantAdd_support L hw r k
    intro q hq
    have h := sup hq
    have p : q∈L.dialogPool.take 515 → q∈L.compactPointPool := fun h => prefixSmall 515 (by omega) h
    rcases hr with rfl|rfl
    all_goals simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢;tauto
  have arith (multiply : Bool) : wires (pointOffsetBorrowedArithmetic L multiply)⊆S :=
    pointOffsetBorrowedArithmetic_compact_support L hw hn multiply
  have square : wires (pointDialogSquare L)⊆S := by
    have sup := pointMeasuredSquareCandidate_support L hw hn
    intro q hq
    have h := sup hq
    have p : q∈L.dialogPool.take 776 → q∈L.compactPointPool := fun h => prefixSmall 776 (by omega) h
    simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have recover : wires (pointRecoveryStage L cx cy)⊆S := by
    have reflect := pointRecoveryReflection_support L hw
    have reflS : wires (pointRecoveryReflection L)⊆S := by
      intro q hq
      have h := reflect hq
      have p : q∈L.dialogPool.take 258 → q∈L.compactPointPool := fun h => prefixSmall 258 (by omega) h
      simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
      tauto
    simpa only [pointRecoveryStage,wires_append,Finset.union_subset_iff] using
      And.intro (And.intro reflS (ca L.point.x (Or.inl rfl) (cx+1))) (ca L.point.y (Or.inr rfl) (-cy))
  simpa only [pointDialogGeneric,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (And.intro (And.intro (And.intro (And.intro
      (ca L.point.x (Or.inl rfl) (-cx)) (ca L.point.y (Or.inr rfl) (-cy)))
      (arith false)) square) (ca L.point.x (Or.inl rfl) (3*cx))) (arith true)) recover

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.pointDialogGeneric_compact_wires
