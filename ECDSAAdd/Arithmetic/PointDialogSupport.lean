import ECDSAAdd.Arithmetic.PointDialogProgram
import ECDSAAdd.Arithmetic.PointInPlaceSupport
import ECDSAAdd.Arithmetic.OffsetBorrowedSupportPoint

set_option maxHeartbeats 3000000

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

attribute [local irreducible] pointOffsetBorrowedArithmetic directSkywalkArithmetic directZeroControlled
  pointRecoveryConstantAdd compactRecoveryConstant pointRecoveryReflection CompactRecoveryNegateLayout.reflection

theorem dialogPort_wires (L : ControlledPointLayout) (hw : L.Widths) :
    L.dialogPort.wires.toFinset=(L.core.generic::L.point.x++L.point.y++L.dialogPool).toFinset := by
  have hp := DialogLayout.fromPool_wires_perm L.core.poolWire L.core.generic L.point.x L.point.y
    hw.inputX hw.inputY
  rw [L.core.pool_prefix hw 2613 (by omega)] at hp
  exact List.toFinset_eq_of_perm _ _ hp

theorem pointDialogGeneric_small_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) :
    wires (pointDialogGeneric L cx cy)⊆(L.core.generic::L.point.x++L.point.y++L.dialogPool.take 1805).toFinset := by
  let S := (L.core.generic::L.point.x++L.point.y++L.dialogPool.take 1805).toFinset
  have prefixSmall (n : Nat) (hn : n≤1805) : L.dialogPool.take n⊆L.dialogPool.take 1805 := by
    intro q hq
    have e : (L.dialogPool.take 1805).take n=L.dialogPool.take n := by
      rw [List.take_take,Nat.min_eq_left hn]
    rw [←e] at hq
    exact List.mem_of_mem_take hq
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (pointDialogConstantAdd L r k)⊆S := by
    have sup := pointRecoveryConstantAdd_support L hw r k
    intro q hq
    have h := sup hq
    have p : q∈L.dialogPool.take 515 → q∈L.dialogPool.take 1805 := fun h => prefixSmall 515 (by omega) h
    rcases hr with rfl|rfl
    all_goals simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢;tauto
  have arith (multiply : Bool) : wires (pointOffsetBorrowedArithmetic L multiply)⊆S := by
    have sup := pointOffsetBorrowedArithmetic_compact_support L hw hn multiply
    have pool : L.compactPointPool⊆L.dialogPool.take 1805 := by
      intro q hq
      have whole : L.dialogPool.take 1805=wireBlock L.core.poolWire 0 1805 := by
        rw [L.core.pool_prefix hw 1805 (by omega)]
        simp [dialogPool,List.take_take]
      rw [whole]
      simp only [compactPointPool,List.mem_append] at hq
      rcases hq with hq|hq
      all_goals
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
        simp only [List.mem_range'_1] at hi
        exact DirectSkywalk.arith_mem L.core.poolWire 0 1805 i (by omega) (by omega)
    intro q hq
    have h := sup hq
    simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    have subset : q∈L.compactPointPool → q∈L.dialogPool.take 1805 := fun hq => pool hq
    tauto
  have square : wires (pointDialogSquare L)⊆S := by
    have sup := pointMeasuredSquareCandidate_support L hw hn
    intro q hq
    have h := sup hq
    have p : q∈L.dialogPool.take 776 → q∈L.dialogPool.take 1805 := fun h => prefixSmall 776 (by omega) h
    simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have recover : wires (pointRecoveryStage L cx cy)⊆S := by
    have reflect := pointRecoveryReflection_support L hw
    have reflS : wires (pointRecoveryReflection L)⊆S := by
      intro q hq
      have h := reflect hq
      have p : q∈L.dialogPool.take 258 → q∈L.dialogPool.take 1805 := fun h => prefixSmall 258 (by omega) h
      simp only [S,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
      tauto
    simpa only [pointRecoveryStage,wires_append,Finset.union_subset_iff] using
      And.intro (And.intro reflS (ca L.point.x (Or.inl rfl) (cx+1))) (ca L.point.y (Or.inr rfl) (-cy))
  simpa only [pointDialogGeneric,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (And.intro (And.intro (And.intro (And.intro
      (ca L.point.x (Or.inl rfl) (-cx)) (ca L.point.y (Or.inr rfl) (-cy)))
      (arith false)) square) (ca L.point.x (Or.inl rfl) (3*cx))) (arith true)) recover

theorem pointDialogGeneric_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) :
    wires (pointDialogGeneric L cx cy)⊆(L.core.generic::L.point.x++L.point.y++L.dialogPool).toFinset := by
  apply (pointDialogGeneric_small_wires L hw hn cx cy).trans
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
  have subset : q∈L.dialogPool.take 1805 → q∈L.dialogPool := List.mem_of_mem_take
  tauto

end ECDSAAdd.Arithmetic
