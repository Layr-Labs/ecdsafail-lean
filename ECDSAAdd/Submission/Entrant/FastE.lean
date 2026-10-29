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
  exact ⟨⟨⟨⟨⟨⟨⟨ca _ (Or.inl rfl) _, ca _ (Or.inr rfl) _⟩, arithE L hw hn false⟩, fastSquareE L hw hn⟩,
    cr⟩, arithE L hw hn true⟩, cn⟩, ca _ (Or.inr rfl) _⟩

theorem fastGeneric_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (fastGeneric2 L cx cy) :=
  fun R b f hg => fast2_boundary_generic L hw hn R b f hc hg

end

end ECDSAAdd.Entrant
