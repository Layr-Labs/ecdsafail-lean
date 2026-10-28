import ECDSAAdd.Arithmetic.CompressedPointDialogProgram
import ECDSAAdd.Arithmetic.PointDialogCounts
import ECDSAAdd.Arithmetic.PointDialogWires
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.CompressedPointDialog
open ControlledPointLayout Secp256k1 MappedCompressed
attribute [local irreducible] wires pointCompressedArithmetic CompressedPointSquare.computableProgram
  pointRecoveryConstantAdd pointRecoveryReflection compactRecoveryConstant
  CompactRecoveryNegateLayout.reflection

def sites (L : ControlledPointLayout) : List Wire :=
  CompressedPointSquare.residents L++CompressedPointSquare.sharedPool L

theorem prefix_small (L : ControlledPointLayout) (hw : L.Widths) (n : Nat) (hn : n ≤ 515) :
    L.dialogPool.take n ⊆ CompressedPointSquare.sharedPool L := by
  have pref : (L.dialogPool.take 515).take n=L.dialogPool.take n := by
    rw [List.take_take,Nat.min_eq_left hn]
  have whole : L.dialogPool.take 515=wireBlock L.core.poolWire 0 515 := by
    simp only [dialogPool,List.take_take,Nat.min_eq_left (show 515 ≤ 2613 by omega)]
    exact (L.core.pool_prefix hw 515 (by omega)).symm
  intro q hq
  rw [←pref] at hq
  have mem := List.mem_of_mem_take hq
  rw [whole] at mem
  exact List.mem_append_left _ (List.mem_append_left _ mem)

theorem generic_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (pointCompressedDialogGeneric L cx cy)⊆(sites L).toFinset := by
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (pointDialogConstantAdd L r k)⊆(sites L).toFinset := by
    have sup := pointRecoveryConstantAdd_support L hw r k
    intro q hq
    have h := sup hq
    have small := prefix_small L hw 515 (Nat.le_refl 515)
    rcases hr with rfl|rfl
    all_goals
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
      simp only [sites,CompressedPointSquare.residents,PointAddLayout.pointWires,inPlaceFlags,
        List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
      have p : q∈L.dialogPool.take 515 → q∈CompressedPointSquare.sharedPool L := fun h => small h
      tauto
  have arith (b : Bool) := pointCompressedArithmetic_support L hw b
  have square := CompressedPointSquare.computable_support L hw hn
  have recover := pointRecoveryStage_support L hw cx cy
  have recovery : wires (pointRecoveryStage L cx cy)⊆(sites L).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (recover hq)
    have p := prefix_small L hw 515 (Nat.le_refl 515)
    simp only [recoveryStageSites,List.mem_append] at h
    simp only [sites,CompressedPointSquare.residents,List.mem_toFinset,List.mem_append]
    tauto
  simpa only [pointCompressedDialogGeneric,wires_append,Finset.union_subset_iff,sites] using
    And.intro (And.intro (And.intro (And.intro (And.intro (And.intro
      (ca L.point.x (Or.inl rfl) (-cx)) (ca L.point.y (Or.inr rfl) (-cy)))
      (arith false)) square) (ca L.point.x (Or.inl rfl) (3*cx))) (arith true)) recovery

theorem generic_counts (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    toffoliCount (pointCompressedDialogGeneric L cx cy)=2213282 ∧
    measurementCount (pointCompressedDialogGeneric L cx cy)=1553824 := by
  have a k := pointDialogConstantAdd_counts L hw hn L.point.x (Or.inl rfl) k
  have b k := pointDialogConstantAdd_counts L hw hn L.point.y (Or.inr rfl) k
  have arith := pointCompressedArithmetic_counts L
  have square := CompressedPointSquare.counts L hw
  have recovery := pointRecoveryStage_counts L hw cx cy
  simp only [pointCompressedDialogGeneric,toffoliCount_append,measurementCount_append,
    (a _).1,(a _).2,(b _).1,(b _).2,arith.1,arith.2.1,arith.2.2.1,arith.2.2.2,
    square.1,square.2,recovery.1,recovery.2]
  norm_num

theorem finite_counts (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    toffoliCount (pointCompressedDialogFinite L C cx cy)=2217386 ∧
    measurementCount (pointCompressedDialogFinite L C cx cy)=1557928 := by
  have hg := generic_counts L hw hn cx cy
  have hz c t k := equalConstant_counts c t L.dialogPointZero k
  have hpl : (PointAddLayout.pointWires L.point).length=513 := by
    simp only [PointAddLayout.pointWires,List.length_cons,List.length_append,
      show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY]
  have hzl : L.dialogPointZero.length=513 := by
    have he := (zeroPorts_maps (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp only [List.length_take,L.dialogPool_length hw]; exact hpl)).1
    simpa only [List.length_map,hpl] using congrArg List.length he
  have he : toffoliCount (pointInPlaceDoubleEnable L cy)=0 ∧
      measurementCount (pointInPlaceDoubleEnable L cy)=0 := by
    unfold pointInPlaceDoubleEnable
    split <;> simp [toffoliCount,measurementCount]
  have hh : toffoliCount (pointDialogExceptionEnable L C)=0 ∧
      measurementCount (pointDialogExceptionEnable L C)=0 := by
    unfold pointDialogExceptionEnable
    split <;> simp [toffoliCount,measurementCount]
  simp only [pointCompressedDialogFinite,pointDialogCorners,pointInPlaceCorners,toffoliCount_append,
    measurementCount_append,hg.1,hg.2,(hz _ _ _).1,(hz _ _ _).2,hzl,
    (maskedPointConstant_counts _ _ _).1,(maskedPointConstant_counts _ _ _).2,he.1,he.2,hh.1,hh.2]
  norm_num [pointDialogGenericFlag,pointInPlaceGenericFlag,toffoliCount,measurementCount]

private theorem equalPoint_wires (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire) (C : Point) :
    wires (equalConstant c t L.dialogPointZero (pointCode C))=
      (c::t::PointAddLayout.pointWires L.point++L.dialogPool.take 513).toFinset := by
  rw [equalConstant_wires]
  have hp := zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
    (by simp [PointAddLayout.pointWires,show L.point.x.length=256 from hw.inputX,
      show L.point.y.length=256 from hw.inputY,L.dialogPool_length hw])
  simp only [dialogPointZero,List.toFinset_cons]
  rw [List.toFinset_eq_of_perm _ _ hp]
  simp only [List.cons_append,List.toFinset_cons]

private theorem genericFlag_wires (L : ControlledPointLayout) : wires (pointInPlaceGenericFlag L)=
    [L.control,L.infinitySelect,L.doubleSelect,L.genericSelect,L.core.generic].toFinset := by
  ext q
  simp only [pointInPlaceGenericFlag,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

theorem finite_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    wires (pointCompressedDialogFinite L C cx cy)⊆(sites L).toFinset := by
  have hGU := generic_support L hw hn cx cy
  have hE := equalPoint_wires L hw
  have hB : (L.dialogPool.take 513).toFinset⊆(sites L).toFinset := by
    intro q hq
    have hm := prefix_small L hw 513 (by omega) (List.mem_toFinset.mp hq)
    simp [sites,CompressedPointSquare.residents,hm]
  have hM (c : Wire) (hc : c∈L.inPlaceFlags) (P : Point) :
      wires (maskedPointConstant c L.point P)⊆(sites L).toFinset := by
    apply (maskedPointConstant_support _ _ _).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq
    rcases hq with rfl|hq
    · simp [sites,CompressedPointSquare.residents,hc]
    · simp [sites,CompressedPointSquare.residents,hq]
  have hO := hM L.infinitySelect (by simp [inPlaceFlags]) C
  have hD := hM L.doubleSelect (by simp [inPlaceFlags]) C
  have hDD := hM L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have hI := hM L.genericSelect (by simp [inPlaceFlags]) (-C)
  have hHE := hM L.core.equalNegY (by simp [inPlaceFlags]) (dialogExceptionPoint C)
  have hHI := hM L.core.equalNegY (by simp [inPlaceFlags]) (-C)
  have hH : wires (pointInPlaceDoubleEnable L cy)⊆[L.control,L.core.double].toFinset := by
    by_cases hh : cy≠-cy <;> simp [pointInPlaceDoubleEnable,hh,wires,Instr.wires]
  have hEX : wires (pointDialogExceptionEnable L C)⊆[L.control,L.core.equalX].toFinset := by
    unfold pointDialogExceptionEnable
    split <;> simp [wires,Instr.wires]
  have hF := genericFlag_wires L
  rw [pointCompressedDialogFinite]
  simp only [wires_append,hE,pointDialogGenericFlag,wires_append,hF,pointDialogCorners,pointInPlaceCorners,wires_append]
  intro q
  have hgu := @hGU q
  have ho := @hO q
  have hd := @hD q
  have hdd := @hDD q
  have hi := @hI q
  have hb := @hB q
  have hh := @hH q
  have hhe := @hHE q
  have hhi := @hHI q
  have hex := @hEX q
  simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,sites,CompressedPointSquare.residents,
    inPlaceFlags,PointAddLayout.pointWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hgu ho hd hdd hi hb hh hhe hhi hex ⊢
  clear hGU hE hB hM hO hD hDD hI hH hHE hHI hEX hF hw
  grind only

theorem sites_subset (L : ControlledPointLayout) (hw : L.Widths) : sites L⊆L.dialogUsedWires := by
  intro q hq
  simp only [sites,List.mem_append] at hq
  rcases hq with res|pool
  · exact List.mem_append_left _ res
  · have mem : q∈L.dialogPool := by
      simp only [CompressedPointSquare.sharedPool,List.mem_append] at pool
      rcases pool with (pool|pool)|pool
      all_goals
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp pool
        simp only [List.mem_range'_1] at hi
        change L.core.poolWire i∈L.core.pool.take 2613
        rw [←L.core.pool_prefix hw 2613 (by omega)]
        exact List.mem_map.mpr ⟨i,by simp [List.mem_range'_1];omega,rfl⟩
    exact List.mem_append_right _ mem

theorem finite_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    wires (pointCompressedDialogFinite L C cx cy)⊆L.dialogUsedWires.toFinset := by
  apply (finite_support L hw hn C cx cy).trans
  intro q hq
  exact List.mem_toFinset.mpr (sites_subset L hw (List.mem_toFinset.mp hq))

theorem finite_qubits (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    qubitCount (pointCompressedDialogFinite L C cx cy) ≤ 1899 := by
  have length : (sites L).length=1899 := by
    rw [sites,List.length_append,CompressedPointSquare.residents_length L hw,CompressedPointSquare.sharedPool_length]
  change (wires (pointCompressedDialogFinite L C cx cy)).card ≤ 1899
  exact (Finset.card_le_card (finite_support L hw hn C cx cy)).trans ((List.toFinset_card_le _).trans_eq length)

end ECDSAAdd.Arithmetic.CompressedPointDialog
#print axioms ECDSAAdd.Arithmetic.CompressedPointDialog.finite_counts
#print axioms ECDSAAdd.Arithmetic.CompressedPointDialog.finite_support
#print axioms ECDSAAdd.Arithmetic.CompressedPointDialog.finite_qubits
