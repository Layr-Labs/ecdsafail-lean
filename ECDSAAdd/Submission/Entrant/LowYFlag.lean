import ECDSAAdd.Submission.Entrant.ZeroFlag
import ECDSAAdd.Math.AffineFormula
import ECDSAAdd.Arithmetic.PointFixedPrimitivesPhysical

namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout

def lowYWires (r : PointReg) : List Wire := r.finite :: (r.x ++ r.y.take 1)

def lowYWork (L : ControlledPointLayout) : List Wire := (L.dialogPool.take 513).take 258

def lowYCode (R : Point) : Nat := (pointFinite R).toNat+2*(pointX R+2^256*(pointY R % 2))

def lowYEqual (L : ControlledPointLayout) (c t : Wire) (Q : Point) : Program :=
  equalConstant c t (zeroPorts (lowYWires L.point) (lowYWork L)) (lowYCode Q)

private theorem lowYCode_split {f f' a a' b b' K : Nat} (hf : f ≤ 1) (hf' : f' ≤ 1)
    (ha : a < K) (ha' : a' < K) (hb : b < 2) (hb' : b' < 2)
    (h : f+2*(a+K*b)=f'+2*(a'+K*b')) : f=f' ∧ a=a' ∧ b=b' := by
  rcases (show b=0 ∨ b=1 by omega) with rfl | rfl <;>
    rcases (show b'=0 ∨ b'=1 by omega) with rfl | rfl <;>
    refine ⟨?_, ?_, ?_⟩ <;> omega

theorem lowYCode_lt (R : Point) : lowYCode R<2^258 := by
  have hp : ECDSAAdd.p<2^256 := by norm_num [ECDSAAdd.p]
  have hx := (point_coordinates_lt R).1
  have hf : (pointFinite R).toNat ≤ 1 := by cases pointFinite R <;> decide
  have h4 : (2:ℕ)^258=4*2^256 := by norm_num
  unfold lowYCode
  rcases Nat.mod_two_eq_zero_or_one (pointY R) with hb | hb <;> rw [hb] <;> omega

theorem pointFinite_neg_some {x y : Fp} (h : curve.toAffine.Nonsingular x y) :
    pointFinite (-(.some h : Point))=true := by
  rw [WeierstrassCurve.Affine.Point.neg_some]
  simp [pointFinite, coordinates]

theorem lowYCode_eq (R Q : Point) (hQ : pointFinite Q=true) :
    decide (lowYCode R=lowYCode Q)=pointEqual R Q := by
  have hp : ECDSAAdd.p<2^256 := by norm_num [ECDSAAdd.p]
  have hp1 : 1<ECDSAAdd.p := by norm_num [ECDSAAdd.p]
  haveI : Fact (Nat.Prime ECDSAAdd.p) := ⟨Secp256k1.p_prime⟩
  have hodd : ECDSAAdd.p % 2=1 := by omega
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, pointEqual_true_iff]
  constructor
  · intro h
    have h' : (pointFinite R).toNat+2*(pointX R+2^256*(pointY R % 2))=
        (pointFinite Q).toNat+2*(pointX Q+2^256*(pointY Q % 2)) := h
    have hs := lowYCode_split (by cases pointFinite R <;> decide) (by cases pointFinite Q <;> decide)
      ((point_coordinates_lt R).1.trans hp) ((point_coordinates_lt Q).1.trans hp)
      (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h'
    cases Q with
    | zero => simp [pointFinite, coordinates] at hQ
    | @some qx qy hq =>
      cases R with
      | zero => simp [pointFinite, coordinates] at hs
      | @some x y hr =>
        have hx : x=qx := ZMod.val_injective ECDSAAdd.p hs.2.1
        have hy : y.val % 2=qy.val % 2 := hs.2.2
        subst hx
        by_cases hinv : y=-qy
        · by_cases hz : qy=0
          · subst hz
            rw [neg_zero] at hinv
            subst hinv
            rfl
          · have hlt : qy.val<ECDSAAdd.p := ZMod.val_lt qy
            have hcast : ((-qy : Fp).val)=(ECDSAAdd.p-qy.val) % ECDSAAdd.p := by
              rw [sub_eq_add_neg, ZMod.val_add, ZMod.neg_val', Nat.add_mod_mod]
            rw [← hinv] at hcast
            simp [hcast, Nat.mod_eq_of_lt hlt, if_neg hz] at hy
            exfalso
            omega
        · have hyq := y_eq_of_x_eq_of_not_inverse hr hq rfl hinv
          subst hyq
          rfl
  · rintro rfl
    rfl

private theorem regValue_take_one (l : List Wire) (s : BasisState) (hl : l≠[]) :
    regValue (l.take 1) s=regValue l s % 2 := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a l =>
    rw [show (a :: l).take 1=[a] from rfl]
    show (if s a then 1 else 0)+2*0=((if s a then 1 else 0)+2*regValue l s) % 2
    by_cases h : s a <;> simp [h] <;> omega

theorem lowYCode_register (r : PointReg) (R : Point) (s : BasisState)
    (hx : r.x.length=256) (hy : r.y.length=256) (h : Holds.holds s r R) :
    regValue (lowYWires r) s=lowYCode R := by
  have hv := (point_holds r R s).mp h
  have hne : r.y≠[] := fun he => by simp [he] at hy
  change (if s r.finite then 1 else 0)+2*regValue (r.x++r.y.take 1) s=_
  rw [regValue_append,hx,regValue_take_one _ _ hne,hv.1,hv.2.1,hv.2.2]
  dsimp only [lowYCode]
  cases pointFinite R <;> rfl

section Layout
variable (L : ControlledPointLayout) (hw : L.Widths)

include hw in
theorem lowYWires_length : (lowYWires L.point).length=258 := by
  simp only [lowYWires,List.length_cons,List.length_append,List.length_take,
    show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY] <;> omega

include hw in
theorem lowY_length : (lowYWires L.point).length=(lowYWork L).length := by
  rw [lowYWires_length L hw]
  simp only [lowYWork,List.length_take,L.dialogPool_length hw] <;> omega

include hw in
theorem lowYPorts_length : (zeroPorts (lowYWires L.point) (lowYWork L)).length=258 := by
  have he := (zeroPorts_maps _ _ (lowY_length L hw)).1
  simpa only [List.length_map,lowYWires_length L hw] using congrArg List.length he

theorem lowY_sublist (c t : Wire) :
    (c::t::lowYWires L.point++lowYWork L).Sublist
      (c::t::PointAddLayout.pointWires L.point++L.dialogPool.take 513) :=
  (((((List.take_sublist 1 L.point.y).append_left L.point.x).cons₂ L.point.finite).cons₂ t).cons₂ c).append
    (List.take_sublist 258 _)

include hw in
theorem lowYPorts_nodup (hn : L.wires.Nodup) (c t : Wire) (hct : c≠t)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) :
    (c::t::(zeroPorts (lowYWires L.point) (lowYWork L)).flatMap ZeroBit.wires).Nodup :=
  (((zeroPorts_perm _ _ (lowY_length L hw)).cons t).cons c).nodup_iff.mpr
    ((lowY_sublist L c t).nodup (L.dialogPointZero_nodup hn c t hct hc ht))

include hw in
theorem lowYEqual_wires (c t : Wire) (Q : Point) (k : Nat) :
    wires (lowYEqual L c t Q) ⊆ wires (equalConstant c t L.dialogPointZero k) := by
  have hd : (lowYWires L.point).length=(lowYWork L).length := lowY_length L hw
  have hf : (PointAddLayout.pointWires L.point).length=(L.dialogPool.take 513).length := by
    have hpl : (PointAddLayout.pointWires L.point).length=513 := by
      simp only [PointAddLayout.pointWires,List.length_cons,List.length_append,
        show L.point.x.length=256 from hw.inputX,show L.point.y.length=256 from hw.inputY]
    simp only [List.length_take,L.dialogPool_length hw]
    exact hpl
  obtain ⟨hx, hwx⟩ := zeroPorts_maps _ _ hd
  obtain ⟨hfx, hfwx⟩ := zeroPorts_maps _ _ hf
  rw [lowYEqual]
  simp only [equalConstant_wires, lowYWork, lowYWires]
  intro q hq
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, List.mem_flatMap] at hq ⊢
  rcases hq with rfl | rfl | ⟨b, hb, hqb⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · obtain ⟨hbin, hwork⟩ := (List.mem_map.mp hb)
  rw [← hx, ← hwx] at *
  obtain ⟨a, ha, rfl⟩ := hbin
  have hwin : a ∈ L.point.x ++ L.point.y.take 1 ∨ a = L.point.finite := by
    rcases ha with rfl | ha
    · exact Or.inr rfl
    · exact Or.inl ha
  have hsub : a ∈ PointAddLayout.pointWires L.point := by
    rcases hwin with ha | rfl
    · rcases List.mem_append.mp ha with ha | ha
      · simp only [PointAddLayout.pointWires, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl ha)
      · simp only [PointAddLayout.pointWires, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr ((List.take_subset 1 L.point.y).subset ha))
    · simp only [PointAddLayout.pointWires, List.mem_cons]
      exact Or.inl rfl
  simp only [PointAddLayout.pointWires, List.mem_cons, List.mem_append] at hsub ⊢
  refine Or.inr (Or.inr ?_)
  refine List.mem_flatMap.mpr ⟨a, ?_, ?_⟩
  · rw [hfx]
    exact hsub
  · simp only [List.mem_map]
    refine ⟨a, ?_, rfl⟩
    rw [hfwx]
    exact ((List.take_sublist 258 (L.dialogPool.take 513)).subset
      ((List.take_subset _ _).subset hwork))

include hw in
theorem lowYEqual_counts (c t : Wire) (Q : Point) :
    toffoliCount (lowYEqual L c t Q)=258 ∧ measurementCount (lowYEqual L c t Q)=258 := by
  have h := equalConstant_counts c t (zeroPorts (lowYWires L.point) (lowYWork L)) (lowYCode Q)
  rw [lowYPorts_length L hw] at h
  exact h

include hw in
theorem lowYEqual_physical (hn : L.wires.Nodup) (c t : Wire) (Q : Point) (hct : c≠t)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) :
    GatePhysical (lowYEqual L c t Q) :=
  equalConstant_physical _ _ _ _ (lowYPorts_nodup L hw hn c t hct hc ht)

end Layout

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem lowYBoundary_equal (R Q : Point) (hQ : pointFinite Q=true) (b : Bool) (f : BasisState)
    (c t : Wire) (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (hct : c≠t)
    (B : Bool) (hb : (if c=L.control then b else f c)=B) :
    Triple (PointDialogBoundary L R b f)
      (lowYEqual L c t Q)
      (PointDialogBoundary L R b (writeBit f t (f t ^^ (B && pointEqual R Q)))) := by
  have hnd := L.dialogPointZero_nodup hn c t hct hc ht
  have hsub := (lowY_sublist L c t).nodup hnd
  intro s m v
  have hclean : regValue (lowYWork L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq=>(regValue_zero _ _).mp v.clean q
      (List.take_subset _ _ (List.take_subset _ _ hq)))
  have hh := equalPorts_correct c t (lowYWires L.point) (lowYWork L) (lowYCode Q)
    (lowY_length L hw) hsub (by rw [lowYWires_length L hw]; exact lowYCode_lt Q) s m hclean
  rw [lowYCode_register L.point R s.basis hw.inputX hw.inputY v.point,lowYCode_eq R Q hQ] at hh
  have hcval : s.basis c=B := by
    rw [← hb]
    split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  change run (lowYEqual L c t Q) m s=_ at hh
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

theorem lowYFlag_equalO (R Q : Point) (hQ : pointFinite Q=true) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (lowYEqual L L.control L.infinitySelect Q)
      (PointDialogBoundary L R b (dialogFlagState L (O ^^ (b && pointEqual R Q)) D I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := lowYBoundary_equal L hw hn R Q hQ b (dialogFlagState L O D I G E H K)
    L.control L.infinitySelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).1)

theorem lowYFlag_equalD (R Q : Point) (hQ : pointFinite Q=true) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (lowYEqual L L.core.double L.doubleSelect Q)
      (PointDialogBoundary L R b (dialogFlagState L O (D ^^ (K && pointEqual R Q)) I G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := lowYBoundary_equal L hw hn R Q hQ b (dialogFlagState L O D I G E H K)
    L.core.double L.doubleSelect
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) K
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.2.2)
  simp only [hr.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.1)

theorem lowYFlag_equalI (R Q : Point) (hQ : pointFinite Q=true) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (lowYEqual L L.control L.genericSelect Q)
      (PointDialogBoundary L R b (dialogFlagState L O D (I ^^ (b && pointEqual R Q)) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := lowYBoundary_equal L hw hn R Q hQ b (dialogFlagState L O D I G E H K)
    L.control L.genericSelect
    (Or.inl rfl)
    (by simp [inPlaceFlags]) (by tauto) b
    (by simp)
  simp only [hr.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.1)

theorem lowYFlag_equalH (R Q : Point) (hQ : pointFinite Q=true) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (lowYEqual L L.core.equalX L.core.equalNegY Q)
      (PointDialogBoundary L R b (dialogFlagState L O D I G E (H ^^ (E && pointEqual R Q)) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := lowYBoundary_equal L hw hn R Q hQ b (dialogFlagState L O D I G E H K)
    L.core.equalX L.core.equalNegY
    (Or.inr (by simp [inPlaceFlags]))
    (by simp [inPlaceFlags]) (by tauto) E
    (by rw [if_neg (by tauto)]; exact hr.2.2.2.2.1)
  simp only [hr.2.2.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.2.2.1)

end

end ECDSAAdd.Entrant
