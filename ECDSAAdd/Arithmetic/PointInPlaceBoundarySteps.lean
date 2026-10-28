import ECDSAAdd.Arithmetic.PointInPlaceBoundary

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pointBoundary_equal (R C : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (hct : c≠t) (B : Bool)
    (hb : (if c=L.control then b else f c)=B) :
    Triple (PointInPlaceBoundary L R b f)
      (equalConstant c t L.inPlacePointZero (pointCode C))
      (PointInPlaceBoundary L R b (writeBit f t (f t ^^ (B && pointEqual R C)))) := by
  have hnd := L.inPlacePointZero_nodup hw hn c t hct hc ht
  intro s m v
  have hclean : regValue (L.inPlaceBorrow.take 513) s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    apply (regValue_zero _ _).mp v.clean
    have h1 := (List.take_sublist 513 L.inPlaceBorrow).count_le q
    have h2 := L.inPlaceBorrow_count q
    have h3 := List.count_pos_iff.mpr hq
    exact List.count_pos_iff.mp (by omega)
  have hh := equalPoint_correct c t L.point (L.inPlaceBorrow.take 513) R C hw.inputX hw.inputY
    (by simp [L.inPlaceBorrow_length hw]) hnd s m v.point hclean
  have hcval : s.basis c=B := by
    rw [← hb]
    split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  change run (equalConstant c t L.inPlacePointZero (pointCode C)) m s=_ at hh
  refine ⟨by rw [hh],v.withFlags hw hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=t
    · subst q; simp [writeBit,hcval,v.flags t ht]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠t := fun he => hq (he ▸ ht)
    simp [writeBit,hqt]

theorem pointBoundary_genericFlag (R : Point) (b : Bool) (f : BasisState) :
    Triple (PointInPlaceBoundary L R b f) (pointInPlaceGenericFlag L)
      (PointInPlaceBoundary L R b (writeBit f L.core.generic
        ((((f L.core.generic ^^ b) ^^ f L.infinitySelect) ^^ f L.doubleSelect) ^^ f L.genericSelect))) := by
  intro s m v
  have hh := pointInPlaceGenericFlag_correct L hw hn s m
  refine ⟨by rw [hh],v.withFlags hw hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=L.core.generic
    · subst q
      simp [writeBit,v.control,v.flags L.core.generic (by simp [inPlaceFlags]),
        v.flags L.infinitySelect (by simp [inPlaceFlags]),v.flags L.doubleSelect (by simp [inPlaceFlags]),
        v.flags L.genericSelect (by simp [inPlaceFlags])]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠L.core.generic := fun he => hq (by simp [he,inPlaceFlags])
    simp [writeBit,hqt]

theorem pointBoundary_doubleEnable (R : Point) (b : Bool) (f : BasisState) (cy : Fp) :
    Triple (PointInPlaceBoundary L R b f) (pointInPlaceDoubleEnable L cy)
      (PointInPlaceBoundary L R b (writeBit f L.core.double
        (f L.core.double ^^ (b && decide (cy≠-cy))))) := by
  intro s m v
  have hh := pointInPlaceDoubleEnable_correct L cy s m
  refine ⟨by rw [hh],v.withFlags hw hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=L.core.double
    · subst q; simp [writeBit,v.control,v.flags L.core.double (by simp [inPlaceFlags])]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠L.core.double := fun he => hq (by simp [he,inPlaceFlags])
    simp [writeBit,hqt]

theorem pointBoundary_generic (R : Point) (b : Bool) (f : BasisState) {cx cy : Fp}
    (hc : curve.toAffine.Nonsingular cx cy)
    (he : f L.core.equalX=false) (hq : f L.core.equalNegY=false)
    (hg : f L.core.generic=true → R≠0 ∧ R≠(.some hc : Point) ∧ R≠-(.some hc : Point)) :
    Triple (PointInPlaceBoundary L R b f) (pointInPlaceGeneric L cx cy (exceptionalSlope (.some hc)))
      (PointInPlaceBoundary L (if f L.core.generic then R+.some hc else R) b f) := by
  intro s m v
  obtain ⟨hp,hr,hf⟩ := pointInPlaceGeneric_point L hw hn R hc (f L.core.generic) hg s m v.point (v.values he hq)
  exact ⟨hp,v.withPoint hw hn hr hf⟩

end ECDSAAdd.Arithmetic
