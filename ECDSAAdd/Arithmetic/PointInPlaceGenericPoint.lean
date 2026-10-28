import ECDSAAdd.Arithmetic.PointInPlaceSupport

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 普通分支对合法点的语义；不选中时允许输入为O或任意角落点。 -/
theorem pointInPlaceGeneric_point (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (G : Bool)
    (hg : G=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point))
    (s : State) (m : List Bool) (hp : Holds.holds s.basis L.point R)
    (hv : PointInPlaceValues L ((coordinates R).getD (0,0)).1
      ((coordinates R).getD (0,0)).2 0 G false false s.basis) :
    let t := run (pointInPlaceGeneric L cx cy (exceptionalSlope (.some hc))) m s
    t.phase=s.phase ∧ Holds.holds t.basis L.point (if G then R+.some hc else R) ∧
      (∀ q∉PointAddLayout.pointWires L.point,t.basis q=s.basis q) := by
  have hfinite : L.point.finite∉L.point.x ∧ L.point.finite∉L.point.y := by
    have hh := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) L.point.finite
    simp only [PointAddLayout.pointWires,List.count_append,List.count_cons,beq_self_eq_true,if_true] at hh
    constructor <;> intro he <;> have ht := List.count_pos_iff.mpr he <;> omega
  have outside (q : Wire) (hq : q∉PointAddLayout.pointWires L.point) : q∉L.point.x ∧ q∉L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_cons,List.mem_append,not_or] at hq
    exact ⟨hq.1.2,hq.2⟩
  cases G with
  | false =>
    obtain ⟨hphase,hv'⟩ := pointInPlaceGeneric_false L hw hn _ _ cx cy (exceptionalSlope (.some hc)) s m hv
    have hf := pointInPlaceGeneric_frame L hw hn cx cy (exceptionalSlope (.some hc)) _ _ _ _ false s m hv hv'
    refine ⟨hphase,?_,fun q hq => hf q (outside q hq).1 (outside q hq).2⟩
    apply (point_holds _ _ _).mpr
    exact ⟨(hf _ hfinite.1 hfinite.2).trans ((point_holds _ _ _).mp hp).1,hv'.x,hv'.y⟩
  | true =>
    have hh := (ordinary_point_iff R hc).mpr (hg rfl)
    cases R with
    | zero => simp [coordinates] at hh
    | @some x y hr =>
      have hx : x≠cx := hh.2
      obtain ⟨hphase,hv'⟩ := pointInPlaceGeneric_true L hw hn x y cx cy (exceptionalSlope (.some hc)) hx
        (exceptional_slope_eq hr hc hx) s m hv
      have hf := pointInPlaceGeneric_frame L hw hn cx cy (exceptionalSlope (.some hc)) _ _ _ _ true s m hv hv'
      refine ⟨hphase,?_,fun q hq => hf q (outside q hq).1 (outside q hq).2⟩
      simp only [if_true,← genericAdd_correct hr hc hx,genericAdd]
      apply (point_holds _ _ _).mpr
      exact ⟨(hf _ hfinite.1 hfinite.2).trans ((point_holds _ _ _).mp hp).1,hv'.x,hv'.y⟩

end ECDSAAdd.Arithmetic
