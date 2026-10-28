import ECDSAAdd.Arithmetic.PointDialogFlagState

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

omit hw in
theorem dialogFlag_separation : (L.control::L.inPlaceFlags).Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  simp only [dialogUsedWires,List.count_append,List.count_cons] at h ⊢
  omega

theorem dialogFlag_equalO (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode C))
      (PointDialogBoundary L R b (dialogFlagState L (O ^^ (b && pointEqual R C)) D I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := dialogBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.control L.infinitySelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).1)

theorem dialogFlag_equalD (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode C))
      (PointDialogBoundary L R b (dialogFlagState L O (D ^^ (K && pointEqual R C)) I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := dialogBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.core.double L.doubleSelect
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) K
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.2.2)
  simp only [hr.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.1)

theorem dialogFlag_equalI (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (equalConstant L.control L.genericSelect L.dialogPointZero (pointCode C))
      (PointDialogBoundary L R b (dialogFlagState L O D (I ^^ (b && pointEqual R C)) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := dialogBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.control L.genericSelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.1)

theorem dialogFlag_equalH (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode C))
      (PointDialogBoundary L R b (dialogFlagState L O D I G E (H ^^ (E && pointEqual R C)) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := dialogBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.core.equalX L.core.equalNegY
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) E
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.1)
  simp only [hr.2.2.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.2.1)

omit hw in
theorem dialogFlag_doubleEnable (R : Point) (b O D I G E H K : Bool) (cy : Fp) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (pointInPlaceDoubleEnable L cy)
      (PointDialogBoundary L R b (dialogFlagState L O D I G E H (K ^^ (b && decide (cy≠-cy))))) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := dialogBoundary_doubleEnable L hn R b (dialogFlagState L O D I G E H K) cy
  simp only [hr.2.2.2.2.2.2] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.2.2)

omit hw in
theorem dialogFlag_exceptionEnable (R : Point) (b O D I G E H K : Bool) (C : Point) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (pointDialogExceptionEnable L C)
      (PointDialogBoundary L R b (dialogFlagState L O D I G (E ^^ (b && (!pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C && !pointEqual (dialogExceptionPoint C) (-C)))) H K)) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := dialogBoundary_exceptionEnable L hn R C b (dialogFlagState L O D I G E H K)
  simp only [hr.2.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.1)

theorem dialogFlag_generic (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (pointDialogGenericFlag L)
      (PointDialogBoundary L R b (dialogFlagState L O D I (((((G ^^ b) ^^ O) ^^ D) ^^ I) ^^ H) E H K)) := by
  have hr := dialogFlagState_read L hn O D I G E H K
  have h1 := dialogBoundary_genericFlag L hw hn R b (dialogFlagState L O D I G E H K)
  simp only [hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1] at h1
  have h1' := h1.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.1)
  let A := ((((G ^^ b) ^^ O) ^^ D) ^^ I)
  have readA := dialogFlagState_read L hn O D I A E H K
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have h2 := dialogBoundary_cx L hn R b (dialogFlagState L O D I A E H K)
    L.core.equalNegY L.core.generic (Or.inr (by simp [inPlaceFlags])) (by simp [inPlaceFlags]) H
    (by rw [if_neg (by tauto)]; exact readA.2.2.2.2.2.1)
  simp only [readA.2.2.2.1] at h2
  have h2' := h2.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I A E H K _).2.2.2.1)
  exact h1'.seq h2'

end ECDSAAdd.Arithmetic
