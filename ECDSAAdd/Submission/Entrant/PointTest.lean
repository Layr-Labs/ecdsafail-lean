import ECDSAAdd.Submission.Entrant.SharedFacts

/-! Point equality tests on 258 bits.

A valid point is determined by its finite flag, its `x` coordinate and the low
bit of its `y` coordinate: two finite points with the same `x` have `y = ±y'`,
and distinct `y` and `-y` differ in their low bit because `p` is odd.  The
equality test against a classical point therefore reads the finite flag, the
256 `x` bits and one `y` bit instead of the full 513-bit register. -/
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout

/-- Finite flag, `x` and the low bit of `y`, little-endian. -/
def code258 (R : Point) : Nat := (pointFinite R).toNat + 2 * (pointX R + 2 ^ 256 * (pointY R % 2))

def pt258 (L : ControlledPointLayout) : List ZeroBit :=
  zeroPorts ((L.point.finite :: L.point.x) ++ L.point.y.take 1) (L.dialogPool.take 258)

theorem code258_lt (R : Point) : code258 R < 2 ^ 258 := by
  have hp : p < 2 ^ 256 := by norm_num [p]
  have hx := (point_coordinates_lt R).1.trans hp
  have hy : pointY R % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hf : (pointFinite R).toNat ≤ 1 := by cases pointFinite R <;> decide
  unfold code258
  have e : (2:Nat) ^ 258 = 4 * 2 ^ 256 := by
    rw [show (258:ℕ) = 2 + 256 from rfl, pow_add]; norm_num
  rw [e]
  generalize (2:ℕ) ^ 256 = B at hx ⊢
  generalize pointX R = X at hx
  generalize pointY R % 2 = Y at hy
  generalize (pointFinite R).toNat = F at hf
  interval_cases Y <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] <;> omega

theorem code258_eq_iff (R C : Point) : code258 R = code258 C ↔ R = C := by
  constructor
  · intro h
    have hp : p < 2 ^ 256 := by norm_num [p]
    have hxR := (point_coordinates_lt R).1.trans hp
    have hxC := (point_coordinates_lt C).1.trans hp
    have hyR : pointY R % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hyC : pointY C % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hf : pointFinite R = pointFinite C := by
      unfold code258 at h
      cases hr : pointFinite R <;> cases hc : pointFinite C <;>
        simp only [hr, hc, Bool.toNat_false, Bool.toNat_true] at h <;> first | rfl | omega
    have hxy : pointX R = pointX C ∧ pointY R % 2 = pointY C % 2 := by
      unfold code258 at h
      rw [hf] at h
      have h' : pointX R + 2 ^ 256 * (pointY R % 2) = pointX C + 2 ^ 256 * (pointY C % 2) := by
        omega
      generalize (2:ℕ) ^ 256 = B at hxR hxC h'
      generalize pointX R = a at hxR h'
      generalize pointX C = c at hxC h'
      generalize pointY R % 2 = b at hyR h' ⊢
      generalize pointY C % 2 = d at hyC h' ⊢
      interval_cases b <;> interval_cases d <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h' <;>
        omega
    cases R with
    | zero =>
      cases C with
      | zero => rfl
      | some hc => simp [pointFinite, coordinates] at hf
    | @some x y hR =>
      cases C with
      | zero => simp [pointFinite, coordinates] at hf
      | @some u v hC =>
        have hxu : x = u := ZMod.val_injective p (by simpa [pointX, coordinates] using hxy.1)
        subst hxu
        have hpar : y.val % 2 = v.val % 2 := by simpa [pointY, coordinates] using hxy.2
        have hyy := WeierstrassCurve.Affine.Y_eq_of_X_eq hR.1 hC.1 rfl
        rw [negY_eq_neg] at hyy
        simp only [WeierstrassCurve.Affine.Point.some.injEq, true_and]
        rcases hyy with e | e
        · exact e
        · by_cases hv : v = -v
          · rw [e, ← hv]
          · exfalso
            rw [e] at hpar
            exact neg_parity hv hpar
  · rintro rfl
    rfl

theorem decide_code258 (R C : Point) : decide (code258 R = code258 C) = pointEqual R C := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, pointEqual_true_iff, code258_eq_iff]

section
variable (L : ControlledPointLayout) (hw : L.Widths)
include hw

theorem pt258_maps : (pt258 L).map ZeroBit.input = (L.point.finite :: L.point.x) ++ L.point.y.take 1 ∧
    (pt258 L).map ZeroBit.work = L.dialogPool.take 258 :=
  zeroPorts_maps _ _ (by simp [(point_lengths L hw).1, (point_lengths L hw).2, L.dialogPool_length hw])

theorem pt258_length : (pt258 L).length = 258 := by
  have h := congrArg List.length (pt258_maps L hw).1
  simpa [(point_lengths L hw).1, (point_lengths L hw).2] using h

theorem pt258_value (s : BasisState) (R : Point) (h : Holds.holds s L.point R) :
    regValue ((pt258 L).map ZeroBit.input) s = code258 R := by
  have hv := (point_holds _ _ _).mp h
  rw [(pt258_maps L hw).1, regValue_append, regValue_take_one, regValue_cons, hv.1, hv.2.1, hv.2.2]
  have hl : (L.point.finite :: L.point.x).length = 257 := by simp [(point_lengths L hw).1]
  rw [hl]
  unfold code258
  have e : (2:Nat) ^ 257 = 2 * 2 ^ 256 := by
    rw [show (257:ℕ) = 1 + 256 from rfl, pow_add]; norm_num
  rw [e]
  cases pointFinite R <;> simp <;> ring

omit hw in
theorem pt258_nodup_of (hn : L.wires.Nodup) (hw : L.Widths) (c t : Wire) (hct : c ≠ t)
    (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags) :
    (c :: t :: (pt258 L).flatMap ZeroBit.wires).Nodup := by
  have big := L.dialogPointZero_nodup hn c t hct hc ht
  apply List.nodup_iff_count_le_one.mpr
  intro w
  have hb := List.nodup_iff_count_le_one.mp big w
  have hperm := (zeroPorts_perm ((L.point.finite :: L.point.x) ++ L.point.y.take 1) (L.dialogPool.take 258)
    (by simp [(point_lengths L hw).1, (point_lengths L hw).2, L.dialogPool_length hw])).count_eq w
  have hy := (List.take_sublist 1 L.point.y).count_le w
  have hpool : (L.dialogPool.take 258).count w ≤ (L.dialogPool.take 513).count w := by
    have hsub : L.dialogPool.take 258 = (L.dialogPool.take 513).take 258 := by
      rw [List.take_take]; rfl
    rw [hsub]
    exact (List.take_sublist _ _).count_le w
  change (c :: t :: (zeroPorts ((L.point.finite :: L.point.x) ++ L.point.y.take 1)
    (L.dialogPool.take 258)).flatMap ZeroBit.wires).count w ≤ 1
  simp only [PointAddLayout.pointWires, List.count_cons, List.count_append] at hb hperm ⊢
  omega

theorem equal258_run (c t : Wire) (hn : (c :: t :: (pt258 L).flatMap ZeroBit.wires).Nodup)
    (R C : Point) (s : State) (m : List Bool) (hp : Holds.holds s.basis L.point R)
    (hz : ∀ b ∈ pt258 L, s.basis b.work = false) :
    run (equalConstant c t (pt258 L) (code258 C)) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && pointEqual R C))⟩ := by
  have hk : code258 C < 2 ^ (pt258 L).length := by
    rw [pt258_length L hw]; exact code258_lt C
  rw [equalConstant_correct c t (pt258 L) (code258 C) hn hk s m hz, pt258_value L hw _ R hp,
    decide_code258]

theorem boundary_equal258 (hn : L.wires.Nodup) (R C : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags) (hct : c ≠ t) (B : Bool)
    (hb : (if c = L.control then b else f c) = B) :
    Triple (PointDialogBoundary L R b f)
      (equalConstant c t (pt258 L) (code258 C))
      (PointDialogBoundary L R b (writeBit f t (f t ^^ (B && pointEqual R C)))) := by
  have hnd := pt258_nodup_of L hn hw c t hct hc ht
  intro s m v
  have hz : ∀ bb ∈ pt258 L, s.basis bb.work = false := by
    intro bb hb'
    have hmem : bb.work ∈ L.dialogPool.take 258 := by
      rw [← (pt258_maps L hw).2]; exact List.mem_map.mpr ⟨bb, hb', rfl⟩
    exact (regValue_zero _ _).mp v.clean bb.work (List.mem_of_mem_take hmem)
  have hh := equal258_run L hw c t hnd R C s m v.point hz
  have hcval : s.basis c = B := by
    rw [← hb]
    split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q = t
    · subst q; simp [writeBit, hcval, v.flags t ht]
    · simp [writeBit, he, v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q ≠ t := fun he => hq (he ▸ ht)
    simp [writeBit, hqt]

theorem flag_equalD258 (hn : L.wires.Nodup) (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (equalConstant L.core.double L.doubleSelect (pt258 L) (code258 C))
      (PointDialogBoundary L R b (dialogFlagState L O (D ^^ (K && pointEqual R C)) I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := boundary_equal258 L hw hn R C b (dialogFlagState L O D I G E H K) L.core.double L.doubleSelect
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) K
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.2.2)
  simp only [hr.2.1] at hh
  exact hh.conseq (fun _ h => h) (fun _ h => h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.1)

theorem flag_equalH258 (hn : L.wires.Nodup) (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (equalConstant L.core.equalX L.core.equalNegY (pt258 L) (code258 C))
      (PointDialogBoundary L R b (dialogFlagState L O D I G E (H ^^ (E && pointEqual R C)) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := boundary_equal258 L hw hn R C b (dialogFlagState L O D I G E H K) L.core.equalX L.core.equalNegY
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) E
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.1)
  simp only [hr.2.2.2.2.2.1] at hh
  exact hh.conseq (fun _ h => h) (fun _ h => h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.2.1)

theorem equal258_counts (c t : Wire) (k : Nat) :
    toffoliCount (equalConstant c t (pt258 L) k) = 258 ∧
    measurementCount (equalConstant c t (pt258 L) k) = 258 := by
  have h := equalConstant_counts c t (pt258 L) k
  rw [pt258_length L hw] at h
  exact h

theorem equal258_wires (c t : Wire) (k : Nat) :
    wires (equalConstant c t (pt258 L) k) ⊆
      (c :: t :: (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513)).toFinset := by
  rw [equalConstant_wires]
  intro q hq
  simp only [List.mem_toFinset, List.mem_cons] at hq ⊢
  rcases hq with rfl | rfl | hq
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · right; right
    have hp := (zeroPorts_perm ((L.point.finite :: L.point.x) ++ L.point.y.take 1) (L.dialogPool.take 258)
      (by simp [(point_lengths L hw).1, (point_lengths L hw).2, L.dialogPool_length hw])).mem_iff.mp hq
    simp only [List.mem_append, List.mem_cons] at hp
    have hsub : L.dialogPool.take 258 = (L.dialogPool.take 513).take 258 := by
      rw [List.take_take]; rfl
    rcases hp with ((h | h) | h) | h
    · simp [PointAddLayout.pointWires, h]
    · simp [PointAddLayout.pointWires, h]
    · simp [PointAddLayout.pointWires, List.mem_of_mem_take h]
    · rw [hsub] at h; simp [List.mem_of_mem_take h]

theorem equal258_physical (hn : L.wires.Nodup) (c t : Wire) (hct : c ≠ t)
    (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags) (k : Nat) :
    GatePhysical (equalConstant c t (pt258 L) k) :=
  equalConstant_physical c t (pt258 L) k (pt258_nodup_of L hn hw c t hct hc ht)

theorem equal258_gateSlots_le (c t : Wire) (k : Nat) :
    Challenge.gateSlots (equalConstant c t (pt258 L) k) ≤ 2323 := by
  have h := Baselines.equalConstant_gateSlots_le c t (pt258 L) k
  rw [pt258_length L hw] at h
  exact h

end

end ECDSAAdd.Entrant
