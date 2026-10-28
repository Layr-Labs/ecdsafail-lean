import ECDSAAdd.Arithmetic.PointDialogGenericPoint

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem dialogBoundary_equal (R C : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (hct : c≠t) (B : Bool)
    (hb : (if c=L.control then b else f c)=B) :
    Triple (PointDialogBoundary L R b f)
      (equalConstant c t L.dialogPointZero (pointCode C))
      (PointDialogBoundary L R b (writeBit f t (f t ^^ (B && pointEqual R C)))) := by
  have hnd := L.dialogPointZero_nodup hn c t hct hc ht
  intro s m v
  have hclean : regValue (L.dialogPool.take 513) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq=>(regValue_zero _ _).mp v.clean q (List.take_subset _ _ hq))
  have hh := equalPoint_correct c t L.point (L.dialogPool.take 513) R C hw.inputX hw.inputY
    (by simp [L.dialogPool_length hw]) hnd s m v.point hclean
  have hcval : s.basis c=B := by
    rw [← hb]
    split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  change run (equalConstant c t L.dialogPointZero (pointCode C)) m s=_ at hh
  refine ⟨by rw [hh],v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=t
    · subst q; simp [writeBit,hcval,v.flags t ht]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠t := fun he => hq (he ▸ ht)
    simp [writeBit,hqt]

theorem dialogBoundary_genericFlag (R : Point) (b : Bool) (f : BasisState) :
    Triple (PointDialogBoundary L R b f) (pointInPlaceGenericFlag L)
      (PointDialogBoundary L R b (writeBit f L.core.generic
        ((((f L.core.generic ^^ b) ^^ f L.infinitySelect) ^^ f L.doubleSelect) ^^ f L.genericSelect))) := by
  intro s m v
  have hh := pointInPlaceGenericFlag_correct L hw hn s m
  refine ⟨by rw [hh],v.withFlags hn ?_ ?_⟩
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

omit hw in
theorem dialogBoundary_doubleEnable (R : Point) (b : Bool) (f : BasisState) (cy : Fp) :
    Triple (PointDialogBoundary L R b f) (pointInPlaceDoubleEnable L cy)
      (PointDialogBoundary L R b (writeBit f L.core.double
        (f L.core.double ^^ (b && decide (cy≠-cy))))) := by
  intro s m v
  have hh := pointInPlaceDoubleEnable_correct L cy s m
  refine ⟨by rw [hh],v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=L.core.double
    · subst q; simp [writeBit,v.control,v.flags L.core.double (by simp [inPlaceFlags])]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠L.core.double := fun he => hq (by simp [he,inPlaceFlags])
    simp [writeBit,hqt]

omit hw in
theorem dialogBoundary_cx (R : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (B : Bool)
    (hb : (if c=L.control then b else f c)=B) :
    Triple (PointDialogBoundary L R b f) [.CX c t]
      (PointDialogBoundary L R b (writeBit f t (f t ^^ B))) := by
  intro s m v
  have hcval : s.basis c=B := by
    rw [←hb]; split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  refine ⟨rfl,v.withFlags hn ?_ ?_⟩
  · intro q hq
    by_cases he : q=t
    · subst q; simp [run,writeBit,hcval,v.flags t ht]
    · simp [run,writeBit,he,v.flags q hq]
  · intro q hq
    have hqt : q≠t := fun he=>hq (he ▸ ht)
    simp [run,writeBit,hqt]

omit hw in
theorem dialogBoundary_exceptionEnable (R C : Point) (b : Bool) (f : BasisState) :
    Triple (PointDialogBoundary L R b f) (pointDialogExceptionEnable L C)
      (PointDialogBoundary L R b (writeBit f L.core.equalX
        (f L.core.equalX ^^ (b && (!pointEqual (dialogExceptionPoint C) 0 &&
          !pointEqual (dialogExceptionPoint C) C && !pointEqual (dialogExceptionPoint C) (-C)))))) := by
  unfold pointDialogExceptionEnable
  split_ifs with h
  · simpa only [h,Bool.and_true] using dialogBoundary_cx L hn R b f L.control L.core.equalX
      (Or.inl rfl) (by simp [inPlaceFlags]) b (by simp)
  · intro s m v
    refine ⟨rfl,⟨v.point,v.control,?_,v.clean⟩⟩
    intro q hq
    have hf : (!pointEqual (dialogExceptionPoint C) 0 &&
      !pointEqual (dialogExceptionPoint C) C && !pointEqual (dialogExceptionPoint C) (-C))=false :=
      Bool.eq_false_iff.mpr h
    simpa [hf,writeBit] using v.flags q hq

end ECDSAAdd.Arithmetic
