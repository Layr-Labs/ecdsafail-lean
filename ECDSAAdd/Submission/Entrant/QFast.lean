import ECDSAAdd.Submission.Entrant.QSupport
import ECDSAAdd.Submission.Entrant.FastGeneric

/-! Pool site 1801 is also avoided by the compare-first generic stage of `567d130`. -/
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem p1801_fastSites (r : List Wire) (hr : r = L.point.x ∨ r = L.point.y) (P : Program)
    (h : wires P ⊆ (L.core.generic :: (L.recoveryConstant r).wires).toFinset) :
    L.core.poolWire 1801 ∉ wires P := by
  apply p1801_of_subset L hw hn _ 515 (by omega)
  intro q hq
  have h' := List.mem_toFinset.mp (h hq)
  have pool := L.recoveryConstant_pool hw r
  have inpool (hh : q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]) :
      q∈L.dialogPool.take 515 := pool ▸ hh
  have hout : (L.recoveryConstant r).out=r := rfl
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
    or_false] at h'
  rw [hout] at h'
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inpool
  apply List.mem_toFinset.mpr
  simp only [CompressedPointSquare.residents, PointAddLayout.pointWires, inPlaceFlags,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hr with rfl | rfl <;> tauto

attribute [local irreducible] wires fastCandidate in
theorem p1801_fastSquare : L.core.poolWire 1801 ∉ wires (fastSquare L) := by
  rw [fastSquare_eq L hw hn]
  intro hq
  rw [fastSquareN, renameProgram_support] at hq
  obtain ⟨old, used, he⟩ := Finset.mem_image.mp hq
  have supp := fastCandidate_support L hw hn used
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at supp
  have res : old ∈ CompressedPointSquare.residents L ∨ old ∈ L.dialogPool.take 776 := by
    simp only [CompressedPointSquare.residents, PointAddLayout.pointWires, inPlaceFlags,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  rcases res with res | mem
  · rw [CompressedPointSquare.resident_fixed L hw hn old res] at he
    subst he
    exact p1801_not_resident L hw hn res
  · rw [pool_block L hw 776 (by omega)] at mem
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp mem
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show CompressedPointSquare.poolPermutation L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire i) =
        L.core.poolWire (CompressedPointSquare.indexPermutation i) from
      CompressedPointSquare.wire_apply L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) i (by omega)] at he
    have hb := CompressedPointSquare.index_bounded i (by omega)
    have := pool_inj L hw hn _ 1801 (by omega) (by omega) he
    omega

theorem p1801_fastGeneric (cx cy : Fp) :
    L.core.poolWire 1801 ∉ wires (fastGeneric L cx cy) := by
  have ca (r : List Wire) (hr : r = L.point.x ∨ r = L.point.y) (k : Fp) :
      L.core.poolWire 1801 ∉ wires (fastConstAdd L r k) :=
    p1801_fastSites L hw hn r hr _ (FastConst.fastAdd_support _ _ ⟨256,L.recoveryConstant_widths hw r
      (by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY)⟩)
  have cn : L.core.poolWire 1801 ∉ wires (fastConstNeg L cx) :=
    p1801_fastSites L hw hn L.point.x (Or.inl rfl) _
      (FastConst.fastNeg_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩)
  have d := p1801_arith L hw hn false
  have m := p1801_arith L hw hn true
  have s := p1801_fastSquare L hw hn
  simp only [fastGeneric, wires_append, Finset.mem_union, not_or]
  exact ⟨⟨⟨⟨⟨⟨⟨ca L.point.x (Or.inl rfl) (-cx), ca L.point.y (Or.inr rfl) (-cy)⟩, d⟩, s⟩,
    ca L.point.x (Or.inl rfl) (3*cx)⟩, m⟩, cn⟩, ca L.point.y (Or.inr rfl) (-cy)⟩

end
end ECDSAAdd.Entrant
