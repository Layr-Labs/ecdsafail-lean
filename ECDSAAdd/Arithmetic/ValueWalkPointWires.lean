/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
import ECDSAAdd.Arithmetic.ValueWalkPointFiniteSpec
import ECDSAAdd.Arithmetic.ValueWalkPointSupport

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

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

/-- 有限常量点加的完整实际支持等式，包括条件false时仍执行的门列。 -/
theorem valueWalkPointDialogFinite_wires (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point) (cx cy : Fp) :
    wires (valueWalkPointDialogFinite L C cx cy)=L.dialogUsedWires.toFinset := by
  have hG := valueWalkPointDialogGeneric_wires L hw hn cx cy
  have hE := equalPoint_wires L hw
  have hB : (L.dialogPool.take 513).toFinset⊆L.dialogUsedWires.toFinset := by
    intro q hq
    have hh := List.take_subset 513 L.dialogPool (List.mem_toFinset.mp hq)
    simp [dialogUsedWires,hh]
  have hM (c : Wire) (hc : c∈L.inPlaceFlags) (P : Point) :
      wires (maskedPointConstant c L.point P)⊆L.dialogUsedWires.toFinset := by
    apply (maskedPointConstant_support _ _ _).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq
    rcases hq with rfl|hq
    · simp [dialogUsedWires,hc]
    · simp [dialogUsedWires,hq]
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
  rw [valueWalkPointDialogFinite]
  simp only [wires_append,hG,hE,pointDialogGenericFlag,wires_append,hF,pointDialogCorners,pointInPlaceCorners,wires_append]
  apply Finset.Subset.antisymm
  · intro q
    have ho := @hO q
    have hd := @hD q
    have hdd := @hDD q
    have hi := @hI q
    have hb := @hB q
    have hh := @hH q
    have hhe := @hHE q
    have hhi := @hHI q
    have hex := @hEX q
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,dialogUsedWires,
      inPlaceFlags,PointAddLayout.pointWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ho hd hdd hi hb hh hhe hhi hex ⊢
    clear hG hE hB hM hO hD hDD hI hH hHE hHI hEX hF hw
    grind only
  · intro q
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,dialogUsedWires,
      inPlaceFlags,PointAddLayout.pointWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    clear hG hE hB hM hO hD hDD hI hH hHE hHI hEX hF hw
    grind only

end ECDSAAdd.Arithmetic
