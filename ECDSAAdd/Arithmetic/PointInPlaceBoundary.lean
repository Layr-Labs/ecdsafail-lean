import ECDSAAdd.Arithmetic.PointInPlaceFlagGates

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 点加阶段边界：合法点、控制、七个标志以及归零的斜率/求逆区。 -/
structure PointInPlaceBoundary (L : ControlledPointLayout) (R : Point) (b : Bool)
    (f : BasisState) (s : BasisState) : Prop where
  point : Holds.holds s L.point R
  control : s L.control=b
  flags : ∀ q∈L.inPlaceFlags,s q=f q
  slope : regValue L.inPlaceSlope s=0
  clean : regValue L.inPlaceInverse.wires s=0

namespace PointInPlaceBoundary

variable {L : ControlledPointLayout} {R R' : Point} {b : Bool} {f f' s t : BasisState}

private theorem flag_away (hw : L.Widths) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈PointAddLayout.pointWires L.point++[L.control]++L.inPlaceSlope++L.inPlaceInverse.wires) :
    q∉L.inPlaceFlags := by
  intro hf
  have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hf
  simp only [List.count_append,List.count_cons,List.count_nil] at h h1
  omega

/-- 仅更新七个标志时，点、控制和干净工作区保持。 -/
theorem withFlags (hw : L.Widths) (hn : L.wires.Nodup) (v : PointInPlaceBoundary L R b f s)
    (hh : ∀ q∈L.inPlaceFlags,t q=f' q) (he : ∀ q∉L.inPlaceFlags,t q=s q) :
    PointInPlaceBoundary L R b f' t := by
  have hp := (point_holds _ _ _).mp v.point
  have away := flag_away hw hn
  refine ⟨(point_holds _ _ _).mpr ⟨?_,?_,?_⟩,?_,hh,?_,?_⟩
  · exact (he _ (away _ (by simp [PointAddLayout.pointWires]))).trans hp.1
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [PointAddLayout.pointWires,hq])))).trans hp.2.1
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [PointAddLayout.pointWires,hq])))).trans hp.2.2
  · exact (he _ (away _ (by simp))).trans v.control
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans v.slope
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans v.clean

/-- 任意点坐标写回的外部保持会保留控制、标志和干净工作区。 -/
theorem withPoint (hw : L.Widths) (hn : L.wires.Nodup) (v : PointInPlaceBoundary L R b f s)
    (hp : Holds.holds t L.point R') (he : ∀ q∉PointAddLayout.pointWires L.point,t q=s q) :
    PointInPlaceBoundary L R' b f t := by
  have away (q : Wire) (hq : q∈[L.control]++L.inPlaceSlope++L.inPlaceFlags++L.inPlaceInverse.wires) :
      q∉PointAddLayout.pointWires L.point := by
    intro hh
    have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  refine ⟨hp,(he _ (away _ (by simp))).trans v.control,?_,?_,?_⟩
  · intro q hq; exact (he q (away q (by simp [hq]))).trans (v.flags q hq)
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans v.slope
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans v.clean

theorem values (v : PointInPlaceBoundary L R b f s)
    (he : f L.core.equalX=false) (hq : f L.core.equalNegY=false) :
    PointInPlaceValues L ((coordinates R).getD (0,0)).1 ((coordinates R).getD (0,0)).2
      0 (f L.core.generic) false false s := by
  have hp := (point_holds _ _ _).mp v.point
  exact ⟨hp.2.1,hp.2.2,v.slope,v.flags _ (by simp [inPlaceFlags]),
    (v.flags _ (by simp [inPlaceFlags])).trans he,(v.flags _ (by simp [inPlaceFlags])).trans hq,v.clean⟩

end PointInPlaceBoundary
end ECDSAAdd.Arithmetic
