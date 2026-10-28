import ECDSAAdd.Arithmetic.PointInPlaceConstant
import ECDSAAdd.Arithmetic.PointInPlaceProduct
import ECDSAAdd.Arithmetic.PointInPlaceNegate
import ECDSAAdd.Arithmetic.PointInPlaceSquare

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 普通分支边界的直接寄存器断言；求逆布局在这些边界完整清零。 -/
structure PointInPlaceValues (L : ControlledPointLayout) (X Y A : Fp) (G E Q : Bool)
    (s : BasisState) : Prop where
  x : regValue L.point.x s=X.val
  y : regValue L.point.y s=Y.val
  slope : regValue L.inPlaceSlope s=A.val
  generic : s L.core.generic=G
  equal : s L.core.equalX=E
  quotient : s L.core.equalNegY=Q
  clean : regValue L.inPlaceInverse.wires s=0

private theorem state_nodup (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    (L.point.x++L.point.y++L.inPlaceSlope++[L.core.generic,L.core.equalX,L.core.equalNegY]++L.inPlaceInverse.wires).Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hnd) q
  simp only [PointAddLayout.pointWires,inPlaceFlags,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

namespace PointInPlaceValues

variable {L : ControlledPointLayout} {X X' Y Y' A A' : Fp} {G E Q : Bool} {s t : BasisState}

theorem borrow (v : PointInPlaceValues L X Y A G E Q s) : regValue L.inPlaceBorrow s=0 := by
  apply (regValue_zero _ _).mpr; intro q hq
  apply (regValue_zero _ _).mp v.clean
  have hb := L.inPlaceBorrow_count q
  have hp := List.count_pos_iff.mpr hq
  exact List.count_pos_iff.mp (by omega)

theorem withX (hw : L.Widths) (hnd : L.wires.Nodup) (v : PointInPlaceValues L X Y A G E Q s)
    (hx : regValue L.point.x t=X'.val) (hf : ∀ q∉L.point.x,t q=s q) :
    PointInPlaceValues L X' Y A G E Q t := by
  have away (q : Wire) (hq : q∈L.point.y++L.inPlaceSlope++[L.core.generic,L.core.equalX,L.core.equalNegY]++L.inPlaceInverse.wires) :
      q∉L.point.x := by
    have hn := state_nodup L hw hnd
    rw [List.append_assoc,List.append_assoc,List.append_assoc] at hn
    simp only [List.append_assoc] at hq
    exact List.disjoint_right.mp (List.nodup_append'.mp hn).2.2 hq
  refine ⟨hx,?_,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.y
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.slope
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (hf _ (away _ (by simp))).trans v.equal
  · exact (hf _ (away _ (by simp))).trans v.quotient
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean

theorem withY (hw : L.Widths) (hnd : L.wires.Nodup) (v : PointInPlaceValues L X Y A G E Q s)
    (hy : regValue L.point.y t=Y'.val) (hf : ∀ q∉L.point.y,t q=s q) :
    PointInPlaceValues L X Y' A G E Q t := by
  have away (q : Wire) (hq : q∈L.point.x++L.inPlaceSlope++[L.core.generic,L.core.equalX,L.core.equalNegY]++L.inPlaceInverse.wires) :
      q∉L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (state_nodup L hw hnd) q
    have ha := List.count_pos_iff.mpr hq
    have hb := List.count_pos_iff.mpr hh
    simp only [List.count_append] at h ha
    omega
  refine ⟨?_,hy,?_,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.x
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.slope
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (hf _ (away _ (by simp))).trans v.equal
  · exact (hf _ (away _ (by simp))).trans v.quotient
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean

theorem withSlope (hw : L.Widths) (hnd : L.wires.Nodup) (v : PointInPlaceValues L X Y A G E Q s)
    (ha : regValue L.inPlaceSlope t=A'.val) (hf : ∀ q∉L.inPlaceSlope,t q=s q) :
    PointInPlaceValues L X Y A' G E Q t := by
  have away (q : Wire) (hq : q∈L.point.x++L.point.y++[L.core.generic,L.core.equalX,L.core.equalNegY]++L.inPlaceInverse.wires) :
      q∉L.inPlaceSlope := by
    intro hh
    have h := List.nodup_iff_count.mp (state_nodup L hw hnd) q
    have ha := List.count_pos_iff.mpr hq
    have hb := List.count_pos_iff.mpr hh
    simp only [List.count_append] at h ha
    omega
  refine ⟨?_,?_,ha,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.x
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.y
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (hf _ (away _ (by simp))).trans v.equal
  · exact (hf _ (away _ (by simp))).trans v.quotient
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean

theorem withEqual {E' : Bool} (hw : L.Widths) (hnd : L.wires.Nodup) (v : PointInPlaceValues L X Y A G E Q s)
    (he : t L.core.equalX=E') (hf : ∀ q,q≠L.core.equalX → t q=s q) :
    PointInPlaceValues L X Y A G E' Q t := by
  have away (q : Wire) (hq : q∈L.point.x++L.point.y++L.inPlaceSlope++[L.core.generic,L.core.equalNegY]++L.inPlaceInverse.wires) :
      q≠L.core.equalX := by
    intro heq; subst q
    have h := List.nodup_iff_count.mp (state_nodup L hw hnd) L.core.equalX
    have ha := List.count_pos_iff.mpr hq
    simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h ha
    omega
  refine ⟨?_,?_,?_,?_,he,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.x
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.y
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.slope
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (hf _ (away _ (by simp))).trans v.quotient
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean

theorem withQuotient {Q' : Bool} (hw : L.Widths) (hnd : L.wires.Nodup) (v : PointInPlaceValues L X Y A G E Q s)
    (he : t L.core.equalNegY=Q') (hf : ∀ q,q≠L.core.equalNegY → t q=s q) :
    PointInPlaceValues L X Y A G E Q' t := by
  have away (q : Wire) (hq : q∈L.point.x++L.point.y++L.inPlaceSlope++[L.core.generic,L.core.equalX]++L.inPlaceInverse.wires) :
      q≠L.core.equalNegY := by
    intro heq; subst q
    have h := List.nodup_iff_count.mp (state_nodup L hw hnd) L.core.equalNegY
    have ha := List.count_pos_iff.mpr hq
    simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h ha
    omega
  refine ⟨?_,?_,?_,?_,?_,he,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.x
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.y
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.slope
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (hf _ (away _ (by simp))).trans v.equal
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean

end PointInPlaceValues
end ECDSAAdd.Arithmetic
