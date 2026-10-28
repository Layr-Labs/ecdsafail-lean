import ECDSAAdd.Arithmetic.PointInPlaceFlagState

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pointFlag_generic (R : Point) (b O D I G H : Bool) :
    Triple (PointInPlaceBoundary L R b (inPlaceFlagState L O D I G H)) (pointInPlaceGenericFlag L)
      (PointInPlaceBoundary L R b (inPlaceFlagState L O D I ((((G ^^ b) ^^ O) ^^ D) ^^ I) H)) := by
  have hh := pointBoundary_genericFlag L hw hn R b (inPlaceFlagState L O D I G H)
  have hr := inPlaceFlagState_read L hw hn O D I G H
  simpa only [hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,(inPlaceFlagState_update L hw hn O D I G H _).2.2.2.1] using hh

theorem pointFlag_doubleEnable (R : Point) (b O D I G H : Bool) (cy : Fp) :
    Triple (PointInPlaceBoundary L R b (inPlaceFlagState L O D I G H)) (pointInPlaceDoubleEnable L cy)
      (PointInPlaceBoundary L R b (inPlaceFlagState L O D I G (H ^^ (b && decide (cy≠-cy))))) := by
  have hh := pointBoundary_doubleEnable L hw hn R b (inPlaceFlagState L O D I G H) cy
  have hr := inPlaceFlagState_read L hw hn O D I G H
  simpa only [hr.2.2.2.2.2.2,(inPlaceFlagState_update L hw hn O D I G H _).2.2.2.2] using hh

/-- 分类使用的三个目标均与控制互异；倍点使能也与其目标互异。 -/
theorem pointFlag_separation : L.control≠L.infinitySelect ∧ L.control≠L.genericSelect ∧
    L.core.double≠L.doubleSelect ∧ L.core.double≠L.control := by
  have hh : (L.control::L.inPlaceFlags).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) q
    simp only [List.count_append,List.count_cons] at h ⊢
    omega
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at hh
  tauto

theorem pointFlag_equalO (R C : Point) (b O D I G H : Bool) :
    Triple (PointInPlaceBoundary L R b (inPlaceFlagState L O D I G H))
      (equalConstant L.control L.infinitySelect L.inPlacePointZero (pointCode C))
      (PointInPlaceBoundary L R b (inPlaceFlagState L (O ^^ (b && pointEqual R C)) D I G H)) := by
  have hh := pointBoundary_equal L hw hn R C b (inPlaceFlagState L O D I G H) L.control L.infinitySelect
    (Or.inl rfl) (by simp [inPlaceFlags]) (pointFlag_separation L hw hn).1 b (by simp)
  have hr := inPlaceFlagState_read L hw hn O D I G H
  simpa only [hr.1,(inPlaceFlagState_update L hw hn O D I G H _).1] using hh

theorem pointFlag_equalD (R C : Point) (b O D I G H : Bool) :
    Triple (PointInPlaceBoundary L R b (inPlaceFlagState L O D I G H))
      (equalConstant L.core.double L.doubleSelect L.inPlacePointZero (pointCode C))
      (PointInPlaceBoundary L R b (inPlaceFlagState L O (D ^^ (H && pointEqual R C)) I G H)) := by
  have hr := inPlaceFlagState_read L hw hn O D I G H
  have hh := pointBoundary_equal L hw hn R C b (inPlaceFlagState L O D I G H) L.core.double L.doubleSelect
    (Or.inr (by simp [inPlaceFlags])) (by simp [inPlaceFlags]) (pointFlag_separation L hw hn).2.2.1 H
    (by rw [if_neg (pointFlag_separation L hw hn).2.2.2]; exact hr.2.2.2.2.2.2)
  simpa only [hr.2.1,(inPlaceFlagState_update L hw hn O D I G H _).2.1] using hh

theorem pointFlag_equalI (R C : Point) (b O D I G H : Bool) :
    Triple (PointInPlaceBoundary L R b (inPlaceFlagState L O D I G H))
      (equalConstant L.control L.genericSelect L.inPlacePointZero (pointCode C))
      (PointInPlaceBoundary L R b (inPlaceFlagState L O D (I ^^ (b && pointEqual R C)) G H)) := by
  have hh := pointBoundary_equal L hw hn R C b (inPlaceFlagState L O D I G H) L.control L.genericSelect
    (Or.inl rfl) (by simp [inPlaceFlags]) (pointFlag_separation L hw hn).2.1 b (by simp)
  have hr := inPlaceFlagState_read L hw hn O D I G H
  simpa only [hr.2.2.1,(inPlaceFlagState_update L hw hn O D I G H _).2.2.1] using hh

end ECDSAAdd.Arithmetic
