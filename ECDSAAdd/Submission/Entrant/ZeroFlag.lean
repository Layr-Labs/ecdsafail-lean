import ECDSAAdd.Baselines.SkywalkCertificate

/-! Infinity tests read the finite flag.

Under the canonical encoding, `R = O` exactly when the finite flag of `R` is
clear (infinity is encoded with a clear flag, every finite point with a set
flag).  The two full-register comparisons against `pointCode 0` used by the
Skywalk classification are therefore replaced by a single controlled flag test
`t ^= c ∧ ¬finite`, which has the same effect on every boundary state. -/
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout

/-- `t ^= c ∧ ¬f`. -/
def zeroFlag (f c t : Wire) : Program := [.X f, .CCX c f t, .X f]

theorem zeroFlag_run (f c t : Wire) (hcf : c ≠ f) (hft : f ≠ t)
    (s : State) (m : List Bool) :
    run (zeroFlag f c t) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && !s.basis f))⟩ := by
  simp only [zeroFlag, run]
  congr 1
  funext q
  by_cases hq : q = t
  · subst q
    simp [writeBit, Function.update, hft.symm, hcf]
  · by_cases hqf : q = f
    · subst q
      simp [writeBit, Function.update, hft]
    · simp [writeBit, Function.update, hq, hqf]

theorem pointEqual_zero (R : Point) : pointEqual R 0 = !pointFinite R := by
  cases R with
  | zero =>
    have h0 : pointEqual WeierstrassCurve.Affine.Point.zero 0 = true := (pointEqual_true_iff _ _).mpr rfl
    rw [h0]
    rfl
  | some h =>
    have hne : (WeierstrassCurve.Affine.Point.some h : Point) ≠ 0 :=
      WeierstrassCurve.Affine.Point.some_ne_zero h
    have hf : pointEqual (WeierstrassCurve.Affine.Point.some h) 0 = false := by
      cases hh : pointEqual (WeierstrassCurve.Affine.Point.some h) 0
      · rfl
      · exact absurd ((pointEqual_true_iff _ _).mp hh) hne
    rw [hf]
    simp [pointFinite, coordinates]

section
variable (L : ControlledPointLayout) (hn : L.wires.Nodup)
include hn

theorem zeroFlag_boundary (R : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (hct : c≠t) (B : Bool)
    (hb : (if c=L.control then b else f c)=B) :
    Triple (PointDialogBoundary L R b f)
      (zeroFlag L.point.finite c t)
      (PointDialogBoundary L R b (writeBit f t (f t ^^ (B && pointEqual R 0)))) := by
  have hnd := L.dialogPointZero_nodup hn c t hct hc ht
  simp only [PointAddLayout.pointWires, List.cons_append, List.nodup_cons, List.mem_cons,
    List.mem_append, not_or] at hnd
  have hcf : c ≠ L.point.finite := hnd.1.2.1
  have hft : L.point.finite ≠ t := fun h => hnd.2.1.1 h.symm
  intro s m v
  have hh := zeroFlag_run L.point.finite c t hcf hft s m
  have hfin : s.basis L.point.finite = pointFinite R := ((point_holds _ _ _).mp v.point).1
  have hcval : s.basis c=B := by
    rw [← hb]
    split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  rw [hfin, ← pointEqual_zero] at hh
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=t
    · subst q; simp [writeBit,hcval,v.flags t ht]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠t := fun he => hq (he ▸ ht)
    simp [writeBit,hqt]

theorem zeroFlag_equalO (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (zeroFlag L.point.finite L.control L.infinitySelect)
      (PointDialogBoundary L R b (dialogFlagState L (O ^^ (b && pointEqual R 0)) D I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := zeroFlag_boundary L hn R b (dialogFlagState L O D I G E H K) L.control L.infinitySelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).1)

theorem zeroFlag_equalI (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (zeroFlag L.point.finite L.control L.genericSelect)
      (PointDialogBoundary L R b (dialogFlagState L O D (I ^^ (b && pointEqual R 0)) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := zeroFlag_boundary L hn R b (dialogFlagState L O D I G E H K) L.control L.genericSelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.1)

end

end ECDSAAdd.Entrant
