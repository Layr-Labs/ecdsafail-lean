import ECDSAAdd.Submission.Entrant.ZeroFlag
import Mathlib.Tactic.ReduceModChar

namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines

def shortSrc (L : ControlledPointLayout) : List Wire :=
  L.point.x ++ L.point.y.take 1

/-- The matching prefix of `pointCode`. -/
def shortCode (R : Point) : Nat :=
  pointX R + 2^256 * (pointY R % 2)

def shortEqual (L : ControlledPointLayout) (c t : Wire) (C : Point) : Program :=
  equalConstant c t (zeroPorts (shortSrc L) (L.dialogPool.take 257)) (shortCode C)

theorem seven_lit : (7 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663) ^ 57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem seven_pow : (7 : Fp) ^ ((p - 1) / 2) = -1 := by
  have hp : 115792089237316195423570985008687907853269984665640564039457584007908834671663 = p := by
    norm_num [p]
  have he : (p - 1) / 2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by
    rw [← hp]
  rw [he]
  have h := hp ▸ seven_lit
  exact h

theorem x_ne_zero {x y : Fp} (h : curve.toAffine.Nonsingular x y) : x ≠ 0 := by
  intro hx
  subst hx
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp [curve, curveA, curveB] at heq
  haveI : Fact (Nat.Prime p) := ⟨Secp256k1.p_prime⟩
  have hy : y ≠ 0 := by
    rintro rfl
    have h7 : ((7 : ℕ) : Fp) = 0 := by exact_mod_cast heq.symm.trans (by ring)
    rw [ZMod.natCast_eq_zero_iff] at h7
    norm_num [p] at h7
  have h1 : y ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hy
  have hodd : p - 1 = 2 * ((p - 1) / 2) := by norm_num [p]
  rw [hodd, pow_mul, heq, seven_pow] at h1
  have h2 : ((2 : ℕ) : Fp) = 0 := by
    have : (-1 : Fp) + 1 = 1 + 1 := by rw [h1]
    rw [neg_add_cancel] at this
    exact_mod_cast (by rw [this]; norm_num : (2 : Fp) = 0)
  rw [ZMod.natCast_eq_zero_iff] at h2
  norm_num [p] at h2

theorem shortCode_lt (R : Point) : shortCode R < 2 * 2^256 := by
  have hp : p < 2^256 := by norm_num [p]
  have hx := (point_coordinates_lt R).1
  have hy : pointY R % 2 < 2 := Nat.mod_lt _ (by decide)
  unfold shortCode
  rcases Nat.lt_succ_iff.mp hy |>.lt_or_eq with h | h
  · have : pointY R % 2 = 0 := by omega
    rw [this]; omega
  · rw [h]; omega

theorem shortCode_eq_iff (R C : Point) : shortCode R = shortCode C ↔ R = C := by
  constructor
  · intro h
    have hp : p < 2^256 := by norm_num [p]
    have hxr := (point_coordinates_lt R).1
    have hxc := (point_coordinates_lt C).1
    have hyr : pointY R % 2 < 2 := Nat.mod_lt _ (by decide)
    have hyc : pointY C % 2 < 2 := Nat.mod_lt _ (by decide)
    have hxy : pointX R = pointX C ∧ pointY R % 2 = pointY C % 2 := by
      unfold shortCode at h
      omega
    cases R with
    | zero =>
      cases C with
      | zero => rfl
      | @some u v hc =>
        exfalso
        have h0 : (0 : Fp).val = u.val := hxy.1
        exact x_ne_zero hc (ZMod.val_injective p (by rw [← h0])).symm
    | @some x y hr =>
      cases C with
      | zero =>
        exfalso
        have h0 : x.val = (0 : Fp).val := hxy.1
        exact x_ne_zero hr (ZMod.val_injective p h0)
      | @some u v hc =>
        have heX : x = u := ZMod.val_injective p hxy.1
        have hpar : y.val % 2 = v.val % 2 := hxy.2
        have heY : y = v := by
          by_cases hyv : y = -v
          · by_cases hv0 : v = 0
            · rw [hyv, hv0, neg_zero]
            · exfalso
              have hneg : y.val = p - v.val := by
                rw [hyv, ZMod.neg_val, if_neg hv0]
              have hvl : v.val < p := ZMod.val_lt v
              have hodd : p % 2 = 1 := by norm_num [p]
              omega
          · exact y_eq_of_x_eq_of_not_inverse hr hc heX hyv
        subst u; subst v; rfl
  · rintro rfl; rfl

theorem regValue_take_one (y : List Wire) (s : BasisState) :
    regValue (y.take 1) s = regValue y s % 2 := by
  cases y with
  | nil => simp [regValue]
  | cons w ys =>
    simp only [List.take_succ_cons, List.take_zero]
    change (if s w then 1 else 0) + 2 * 0 = ((if s w then 1 else 0) + 2 * regValue ys s) % 2
    split <;> omega

theorem shortSrc_value (L : ControlledPointLayout) (hw : L.Widths) (R : Point) (s : BasisState)
    (hp : Holds.holds s L.point R) : regValue (shortSrc L) s = shortCode R := by
  have hv := (point_holds L.point R s).mp hp
  rw [shortSrc, regValue_append, show L.point.x.length = 256 from hw.inputX, regValue_take_one,
    hv.2.1, hv.2.2]
  rfl

theorem shortSrc_length (L : ControlledPointLayout) (hw : L.Widths) :
    (shortSrc L).length = 257 := by
  simp [shortSrc, show L.point.x.length = 256 from hw.inputX,
    show L.point.y.length = 256 from hw.inputY]

theorem shortWork_length (L : ControlledPointLayout) (hw : L.Widths) :
    (L.dialogPool.take 257).length = 257 := by
  simp [L.dialogPool_length hw]

theorem short_sublist_inner (L : ControlledPointLayout) :
    (shortSrc L ++ L.dialogPool.take 257).Sublist
      (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513) := by
  have h1 : (shortSrc L).Sublist (PointAddLayout.pointWires L.point) := by
    simp only [shortSrc, PointAddLayout.pointWires, List.cons_append]
    exact ((List.Sublist.refl _).append (List.take_sublist 1 _)).cons _
  have h2 : (L.dialogPool.take 257).Sublist (L.dialogPool.take 513) := by
    have he : L.dialogPool.take 257 = (L.dialogPool.take 513).take 257 := by
      rw [List.take_take]; rfl
    rw [he]; exact List.take_sublist _ _
  exact h1.append h2

theorem short_sublist (L : ControlledPointLayout) (c t : Wire) :
    (c :: t :: shortSrc L ++ L.dialogPool.take 257).Sublist
      (c :: t :: PointAddLayout.pointWires L.point ++ L.dialogPool.take 513) :=
  ((short_sublist_inner L).cons_cons t).cons_cons c

theorem short_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) (c t : Wire) (hct : c ≠ t)
    (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags) :
    (c :: t :: shortSrc L ++ L.dialogPool.take 257).Nodup :=
  (L.dialogPointZero_nodup hn c t hct hc ht).sublist (short_sublist L c t)

theorem shortEqual_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c t : Wire) (hct : c ≠ t) (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags)
    (R C : Point) (s : State) (m : List Bool) (hp : Holds.holds s.basis L.point R)
    (hz : regValue (L.dialogPool.take 257) s.basis = 0) :
    run (shortEqual L c t C) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && pointEqual R C))⟩ := by
  have hh := equalPorts_correct c t (shortSrc L) (L.dialogPool.take 257) (shortCode C)
    ((shortSrc_length L hw).trans (shortWork_length L hw).symm) (short_nodup L hn c t hct hc ht)
    (by rw [shortSrc_length L hw, show (257:ℕ) = 256 + 1 from rfl, Nat.pow_succ, mul_comm]
        exact shortCode_lt C) s m hz
  rw [shortSrc_value L hw R s.basis hp] at hh
  have he : decide (shortCode R = shortCode C) = pointEqual R C := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, shortCode_eq_iff, pointEqual_true_iff]
  rw [he] at hh
  exact hh

/-- Support of the short comparison is inside the support of the full comparison. -/
theorem shortEqual_wires_subset (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire)
    (C : Point) (k : Nat) :
    wires (shortEqual L c t C) ⊆ wires (equalConstant c t L.dialogPointZero k) := by
  have hpl : (PointAddLayout.pointWires L.point).length = (L.dialogPool.take 513).length := by
    simp [PointAddLayout.pointWires, L.dialogPool_length hw,
      show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]
  have hsl := (shortSrc_length L hw).trans (shortWork_length L hw).symm
  rw [shortEqual, equalConstant_wires, equalConstant_wires]
  intro q hq
  simp only [List.mem_toFinset, List.mem_cons] at hq ⊢
  rcases hq with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · have hm := (zeroPorts_perm _ _ hsl).subset h
    exact Or.inr (Or.inr ((zeroPorts_perm _ _ hpl).symm.subset ((short_sublist_inner L).subset hm)))

theorem shortEqual_counts (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire) (C : Point) :
    toffoliCount (shortEqual L c t C) = 257 ∧ measurementCount (shortEqual L c t C) = 257 := by
  have hl : (zeroPorts (shortSrc L) (L.dialogPool.take 257)).length = 257 := by
    have he := (zeroPorts_maps (shortSrc L) (L.dialogPool.take 257)
      ((shortSrc_length L hw).trans (shortWork_length L hw).symm)).1
    simpa only [List.length_map, shortSrc_length L hw] using congrArg List.length he
  have h := equalConstant_counts c t (zeroPorts (shortSrc L) (L.dialogPool.take 257)) (shortCode C)
  rw [hl] at h
  exact h

theorem shortEqual_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c t : Wire) (hct : c ≠ t) (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (ht : t ∈ L.inPlaceFlags)
    (C : Point) : GatePhysical (shortEqual L c t C) := by
  have hsl := (shortSrc_length L hw).trans (shortWork_length L hw).symm
  apply equalConstant_physical
  have hperm := ((zeroPorts_perm _ _ hsl).cons t).cons c
  exact hperm.nodup_iff.mpr (short_nodup L hn c t hct hc ht)

theorem shortEqual_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire)
    (C : Point) : gateSlots (shortEqual L c t C) ≤ 2314 := by
  have hl : (zeroPorts (shortSrc L) (L.dialogPool.take 257)).length = 257 := by
    have he := (zeroPorts_maps (shortSrc L) (L.dialogPool.take 257)
      ((shortSrc_length L hw).trans (shortWork_length L hw).symm)).1
    simpa only [List.length_map, shortSrc_length L hw] using congrArg List.length he
  have h := Baselines.equalConstant_gateSlots_le c t
    (zeroPorts (shortSrc L) (L.dialogPool.take 257)) (shortCode C)
  rw [hl] at h
  exact h

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem shortBoundary_equal (R C : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (hct : c≠t) (B : Bool)
    (hb : (if c=L.control then b else f c)=B) :
    Triple (PointDialogBoundary L R b f)
      (shortEqual L c t C)
      (PointDialogBoundary L R b (writeBit f t (f t ^^ (B && pointEqual R C)))) := by
  intro s m v
  have hclean : regValue (L.dialogPool.take 257) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq=>(regValue_zero _ _).mp v.clean q (List.take_subset _ _ hq))
  have hh := shortEqual_correct L hw hn c t hct hc ht R C s m v.point hclean
  have hcval : s.basis c=B := by
    rw [← hb]
    split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
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

theorem shortFlag_equalO (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (shortEqual L L.control L.infinitySelect C)
      (PointDialogBoundary L R b (dialogFlagState L (O ^^ (b && pointEqual R C)) D I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := shortBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.control L.infinitySelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).1)

theorem shortFlag_equalD (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (shortEqual L L.core.double L.doubleSelect C)
      (PointDialogBoundary L R b (dialogFlagState L O (D ^^ (K && pointEqual R C)) I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := shortBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.core.double L.doubleSelect
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) K
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.2.2)
  simp only [hr.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.1)

theorem shortFlag_equalI (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (shortEqual L L.control L.genericSelect C)
      (PointDialogBoundary L R b (dialogFlagState L O D (I ^^ (b && pointEqual R C)) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := shortBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.control L.genericSelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.1)

theorem shortFlag_equalH (R C : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (shortEqual L L.core.equalX L.core.equalNegY C)
      (PointDialogBoundary L R b (dialogFlagState L O D I G E (H ^^ (E && pointEqual R C)) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := shortBoundary_equal L hw hn R C b (dialogFlagState L O D I G E H K) L.core.equalX L.core.equalNegY
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) E
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.1)
  simp only [hr.2.2.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.2.1)

end

end ECDSAAdd.Entrant
