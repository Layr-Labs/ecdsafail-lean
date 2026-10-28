import ECDSAAdd.Arithmetic.PointDialogConstant
import ECDSAAdd.Arithmetic.PointDialogNegate
import ECDSAAdd.Arithmetic.PointDialogDivide
import ECDSAAdd.Arithmetic.PointDialogSquare

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 六阶段边界只有点坐标存活，池归零，其余线路逐线保持输入快照。 -/
structure PointDialogValues (L : ControlledPointLayout) (X Y : Fp) (G : Bool)
    (base s : BasisState) : Prop where
  x : regValue L.point.x s=X.val
  y : regValue L.point.y s=Y.val
  generic : s L.core.generic=G
  clean : regValue L.dialogPool s=0
  rest : ∀q,q∉L.point.x++L.point.y → s q=base q

namespace PointDialogValues
variable {L : ControlledPointLayout} {X X' Y Y' : Fp} {G : Bool} {base s t : BasisState}

theorem withX (hn : L.wires.Nodup) (v : PointDialogValues L X Y G base s)
    (hx : regValue L.point.x t=X'.val) (hf : ∀q,q∉L.point.x → t q=s q) :
    PointDialogValues L X' Y G base t := by
  have away (q : Wire) (hq : q∈L.point.y++[L.core.generic]++L.dialogPool) : q∉L.point.x := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
      List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  refine ⟨hx,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.y
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean
  · intro q hq; exact (hf q (fun h=>hq (List.mem_append_left _ h))).trans (v.rest q hq)

theorem withY (hn : L.wires.Nodup) (v : PointDialogValues L X Y G base s)
    (hy : regValue L.point.y t=Y'.val) (hf : ∀q,q∉L.point.y → t q=s q) :
    PointDialogValues L X Y' G base t := by
  have away (q : Wire) (hq : q∈L.point.x++[L.core.generic]++L.dialogPool) : q∉L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
      List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  refine ⟨?_,hy,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.x
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean
  · intro q hq; exact (hf q (fun h=>hq (List.mem_append_right _ h))).trans (v.rest q hq)
end PointDialogValues
end ECDSAAdd.Arithmetic
