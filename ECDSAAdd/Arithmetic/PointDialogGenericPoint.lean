import ECDSAAdd.Arithmetic.PointDialogBoundary

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

theorem dialogBoundary_generic (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) (b : Bool) (f : BasisState) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point) ∧
      R≠dialogExceptionPoint (.some hc)) :
    Triple (PointDialogBoundary L R b f) (pointDialogGeneric L cx cy)
      (PointDialogBoundary L (if f L.core.generic then R+.some hc else R) b f) := by
  intro s m v
  have hp := (point_holds _ _ _).mp v.point
  have values : PointDialogValues L ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 (f L.core.generic) s.basis s.basis :=
    ⟨hp.2.1,hp.2.2,v.flags _ (by simp [inPlaceFlags]),v.clean,fun _ _=>rfl⟩
  have hfinite : L.point.finite∉L.point.x++L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have ht := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
      beq_self_eq_true,if_true] at h ht
    omega
  have outside (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) : q∉L.point.x++L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  cases hG : f L.core.generic with
  | false =>
    rw [hG] at values
    obtain ⟨phase,hv⟩ := pointDialogGeneric_false L hw hn _ _ cx cy s.basis s m values
    refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
    simp only [Bool.false_eq_true,if_false]
    exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩
  | true =>
    have he := hg hG
    cases R with
    | zero => exact False.elim (he.1 rfl)
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      rw [hG] at values
      obtain ⟨phase,hv⟩ := pointDialogGeneric_true L hw hn x y cx cy s.basis den.1 den.2 s m values
      refine ⟨phase,v.withPoint hn ?_ (fun q hq=>hv.rest q (outside q hq))⟩
      simp only [if_true,←genericAdd_correct hr hc den.1,genericAdd]
      exact (point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1,hv.x,hv.y⟩

end ECDSAAdd.Arithmetic
