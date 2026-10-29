import ECDSAAdd.Submission.Entrant.FastGeneric
import ECDSAAdd.Submission.Entrant.QSupport

/-! The fast generic stage also avoids pool site 1801: its constant adders
work on the point registers, the generic flag and the first 515 pool sites. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout
attribute [local irreducible] wires pointMeasuredSquareCandidate CompressedPointSquare.computableProgram

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem p1801_fastConst (r : List Wire) (hr : r = L.point.x ∨ r = L.point.y) (P : Program)
    (hP : wires P ⊆ (L.core.generic :: (L.recoveryConstant r).wires).toFinset) :
    L.core.poolWire 1801 ∉ wires P := by
  apply p1801_of_subset L hw hn _ 515 (by omega)
  intro q hq
  have h := List.mem_toFinset.mp (hP hq)
  have pool := L.recoveryConstant_pool hw r
  have inpool (h : q∈(L.recoveryConstant r).src++(L.recoveryConstant r).carry++
      [(L.recoveryConstant r).high,(L.recoveryConstant r).cin,(L.recoveryConstant r).flag]) :
      q∈L.dialogPool.take 515 := pool ▸ h
  have hout : (L.recoveryConstant r).out=r := rfl
  simp only [MeasuredCanonicalModLayout.wires,List.mem_cons,List.mem_append,List.not_mem_nil,
    or_false] at h
  rw [hout] at h
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at inpool
  apply List.mem_toFinset.mpr
  simp only [CompressedPointSquare.residents, PointAddLayout.pointWires, inPlaceFlags,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hr with rfl | rfl <;> tauto

theorem p1801_fastGeneric (cx cy : Fp) :
    L.core.poolWire 1801 ∉ wires (fastGeneric L cx cy) := by
  have ca (r : List Wire) (hr : r = L.point.x ∨ r = L.point.y) (k : Fp) :
      L.core.poolWire 1801 ∉ wires (fastConstAdd L r k) :=
    p1801_fastConst L hw hn r hr _ (FastConst.fastAdd_support _ _ ⟨256,L.recoveryConstant_widths hw r
      (by rcases hr with rfl|rfl;exact hw.inputX;exact hw.inputY)⟩)
  have cn : L.core.poolWire 1801 ∉ wires (fastConstNeg L cx) :=
    p1801_fastConst L hw hn L.point.x (Or.inl rfl) _
      (FastConst.fastNeg_support _ _ ⟨256,L.recoveryConstant_widths hw L.point.x hw.inputX⟩)
  have a1 := ca L.point.x (Or.inl rfl) (-cx)
  have a2 := ca L.point.y (Or.inr rfl) (-cy)
  have a3 := ca L.point.x (Or.inl rfl) (3*cx)
  have a4 := ca L.point.y (Or.inr rfl) (-cy)
  have d := p1801_arith L hw hn false
  have m := p1801_arith L hw hn true
  have s := p1801_square L hw hn
  simp only [fastGeneric, wires_append, Finset.mem_union, not_or]
  exact ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, d⟩, s⟩, a3⟩, m⟩, cn⟩, a4⟩

end

end ECDSAAdd.Entrant
