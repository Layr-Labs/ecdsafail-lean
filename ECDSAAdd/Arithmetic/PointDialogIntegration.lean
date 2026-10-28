import ECDSAAdd.Arithmetic.PointDialogWires
import ECDSAAdd.Arithmetic.PointDialogCounts
import ECDSAAdd.Arithmetic.CompressedPointDialogSpec

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private theorem boundary_frame_values (L : ControlledPointLayout) (P : Program)
    (hP : wires P⊆L.dialogUsedWires.toFinset) (R R' : Point) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (ho : PointDialogBoundary L R' b (fun _ => false) (run P m s).basis)
    (q : Wire) (hp : q∉PointAddLayout.pointWires L.point) : (run P m s).basis q=s.basis q := by
  by_cases hc : q=L.control
  · subst q; exact ho.control.trans hi.control.symm
  by_cases hf : q∈L.inPlaceFlags
  · exact (ho.flags q hf).trans (hi.flags q hf).symm
  by_cases hw : q∈L.dialogPool
  · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw
  apply run_preserves_outside
  apply mt (@hP q)
  simp [dialogUsedWires,hp,hc,hf,hw]

theorem pointDialogFinite_frame (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) :
    (run (pointDialogFinite L (.some hc) cx cy) m s).basis q=s.basis q := by
  have ho := (pointDialogFinite_spec L hw hn R hc b s m hi).2
  exact boundary_frame_values L _ (pointDialogFinite_wires L hw hn (.some hc) cx cy) R _ b s m hi ho q hq

private theorem boundary_work_subset (L : ControlledPointLayout) :
    L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
  omega

private theorem work_not_point (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.work) : q∉PointAddLayout.pointWires L.point := by
  intro hp
  have hh := List.nodup_iff_count.mp hn q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.wires,work,outWork,temporary,point,extras,selectors,PointAddLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at hh h1 h2
  omega

/-- 公共布局的全部分配工作位恢复为零，包括本实现未使用的旧银行。 -/
theorem pointDialogFinite_full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) :
    {{ L.control=b,L.point=R,L.work=0 }} pointCompressedDialogFinite L (.some hc) cx cy
    {{ L.control=b,L.point=(if b then R+.some hc else R),L.work=0 }} := by
  exact CompressedPointDialog.full_spec L hw hn R hc b

end ECDSAAdd.Arithmetic
