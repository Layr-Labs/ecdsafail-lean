import ECDSAAdd.Arithmetic.PointDialogGeneric
import ECDSAAdd.Arithmetic.PointInPlaceFlagGates

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 点加阶段边界：合法点、控制、七个标志以及归零的斜率/求逆区。 -/
structure PointDialogBoundary (L : ControlledPointLayout) (R : Point) (b : Bool)
    (f : BasisState) (s : BasisState) : Prop where
  point : Holds.holds s L.point R
  control : s L.control=b
  flags : ∀ q∈L.inPlaceFlags,s q=f q
  clean : regValue L.dialogPool s=0

namespace PointDialogBoundary

variable {L : ControlledPointLayout} {R R' : Point} {b : Bool} {f f' s t : BasisState}

private theorem flag_away (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈PointAddLayout.pointWires L.point++[L.control]++L.dialogPool) :
    q∉L.inPlaceFlags := by
  intro hf
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hf
  simp only [dialogUsedWires,List.count_append,List.count_cons,List.count_nil] at h h1
  omega

/-- 仅更新七个标志时，点、控制和干净工作区保持。 -/
theorem withFlags (hn : L.wires.Nodup) (v : PointDialogBoundary L R b f s)
    (hh : ∀ q∈L.inPlaceFlags,t q=f' q) (he : ∀ q∉L.inPlaceFlags,t q=s q) :
    PointDialogBoundary L R b f' t := by
  have hp := (point_holds _ _ _).mp v.point
  have away := flag_away hn
  refine ⟨(point_holds _ _ _).mpr ⟨?_,?_,?_⟩,?_,hh,?_⟩
  · exact (he _ (away _ (by simp [PointAddLayout.pointWires]))).trans hp.1
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [PointAddLayout.pointWires,hq])))).trans hp.2.1
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [PointAddLayout.pointWires,hq])))).trans hp.2.2
  · exact (he _ (away _ (by simp))).trans v.control
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans v.clean

/-- 任意点坐标写回的外部保持会保留控制、标志和干净工作区。 -/
theorem withPoint (hn : L.wires.Nodup) (v : PointDialogBoundary L R b f s)
    (hp : Holds.holds t L.point R') (he : ∀ q∉PointAddLayout.pointWires L.point,t q=s q) :
    PointDialogBoundary L R' b f t := by
  have away (q : Wire) (hq : q∈[L.control]++L.inPlaceFlags++L.dialogPool) :
      q∉PointAddLayout.pointWires L.point := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires,List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  refine ⟨hp,(he _ (away _ (by simp))).trans v.control,?_,?_⟩
  · intro q hq; exact (he q (away q (by simp [hq]))).trans (v.flags q hq)
  · exact (regValue_congr _ _ _ (fun q hq => he q (away q (by simp [hq])))).trans v.clean

end PointDialogBoundary
end ECDSAAdd.Arithmetic
