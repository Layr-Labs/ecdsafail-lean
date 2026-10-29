import ECDSAAdd.Submission.Entrant.EKMain
import ECDSAAdd.Submission.Entrant.FastGeneric2

/-! The compare-first generic block lives in `sitesE` and satisfies the
generic-block contract. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog
attribute [local irreducible] wires controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw

theorem fastConstE (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) :
    (L.core.generic::(L.recoveryConstant r).wires).toFinset ⊆ (sitesE L).toFinset := by
  intro q hq
  have pool := L.recoveryConstant_pool hw r
  have hq' := List.mem_toFinset.mp hq
  have inpool (h : q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]) :
      q∈L.dialogPool.take 515 := pool ▸ h
  apply List.mem_toFinset.mpr
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
    or_false] at hq'
  have hout : (L.recoveryConstant r).out=r := rfl
  rw [hout] at hq'
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inpool
  rcases hq' with h | (((h | h) | h) | h | h | h)
  · rw [h]; exact generic_E L
  · exact pool_lowE L hw 515 (by omega) q (inpool (Or.inl (Or.inl h)))
  · rcases hr with rfl | rfl
    · exact x_E L _ h
    · exact y_E L _ h
  · exact pool_lowE L hw 515 (by omega) q (inpool (Or.inl (Or.inr h)))
  · exact pool_lowE L hw 515 (by omega) q (inpool (Or.inr (Or.inl h)))
  · exact pool_lowE L hw 515 (by omega) q (inpool (Or.inr (Or.inr (Or.inl h))))
  · exact pool_lowE L hw 515 (by omega) q (inpool (Or.inr (Or.inr (Or.inr h))))

include hn

attribute [local irreducible] fastCandidateNR in
theorem fastSquareNRE : wires (fastSquareNR L) ⊆ (sitesE L).toFinset := by
  rw [fastSquareNR_eq L hw hn]
  intro q hq
  rw [fastSquareNRN, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  have supp := fastCandidateNR_support L hw hn used
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at supp
  apply List.mem_toFinset.mpr
  rcases supp with h | h | h | h
  · rw [h, CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      inPlaceFlags])]
    exact generic_E L
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact y_E L _ h
  · rw [CompressedPointSquare.resident_fixed L hw hn _ (by simp [CompressedPointSquare.residents,
      PointAddLayout.pointWires, h])]
    exact x_E L _ h
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show CompressedPointSquare.poolPermutation L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) (L.core.poolWire i) =
        L.core.poolWire (CompressedPointSquare.indexPermutation i) from
      CompressedPointSquare.wire_apply L.core.poolWire
        (CompressedPointSquare.layout_bounded_injective L hw hn) i (by omega)]
    apply poolQ_E
    have hb := CompressedPointSquare.index_bounded i (by omega)
    have ha := CompressedPointSquare.prefix_allowed i bound
    simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
    rcases ha with ha | ha
    · exact Or.inl (Or.inl (Or.inl ⟨_, by omega, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨_, by omega, rfl⟩))

theorem fastGenericE (cx cy : Fp) : wires (fastGeneric2 L cx cy) ⊆ (sitesE L).toFinset := by
  have ca (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y) (k : Fp) :
      wires (fastConstAdd L r k) ⊆ (sitesE L).toFinset :=
    (FastConst.fastAdd_support _ _ ⟨256,L.recoveryConstant_widths hw r
      (by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY)⟩).trans
      (fastConstE L hw r hr)
  have cn : wires (fastConstNeg L cx) ⊆ (sitesE L).toFinset :=
    (FastConst.fastNeg_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConstE L hw L.point.x (Or.inl rfl))
  have cr : wires (fastConstRefl L (3*cx-1)) ⊆ (sitesE L).toFinset :=
    (FastConst.fastRefl_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩).trans
      (fastConstE L hw L.point.x (Or.inl rfl))
  simp only [fastGeneric2, wires_append, Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨ca _ (Or.inl rfl) _, ca _ (Or.inr rfl) _⟩, arithE L hw hn false⟩, fastSquareNRE L hw hn⟩,
    cr⟩, arithE L hw hn true⟩, cn⟩, ca _ (Or.inr rfl) _⟩

theorem fastGeneric_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (fastGeneric2 L cx cy) :=
  fun R b f hg => fast2_boundary_generic L hw hn R b f hc hg

end

end ECDSAAdd.Entrant
