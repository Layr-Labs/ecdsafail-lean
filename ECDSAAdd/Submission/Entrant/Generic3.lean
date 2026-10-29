import ECDSAAdd.Submission.Entrant.FastE

/-! Divisor repair from the finite flag.

No secp256k1 point has `x = 0`: `0³ + 7 = 7` is not a square modulo `p`
(quadratic reciprocity, `p ≡ 3 (mod 4)`, `p ≡ 1 (mod 7)`).  In the generic
block the divisor register holds either `x_R` (inactive branch) or a nonzero
difference (active branch), so it is zero exactly when the input point is
infinite, i.e. exactly when the finite flag is clear.

`farith` therefore runs the bare lane kernel (`arith3`, no compare-based zero
repair) between two copies of `x₀ ^= ¬finite`. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog DirectSkywalk
open MappedCompressed.LaneA (laneKernel laneKernel_support laneKernel_counts laneKernel_physical
  laneKernel_gateSlots_le)

section Curve

theorem seven_not_square : ¬ IsSquare (7 : ZMod p) := by
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : legendreSym p 7 = -1 := by
    have hqr := legendreSym.quadratic_reciprocity_three_mod_four (p := 7) (q := p)
      (by norm_num) (by norm_num [p])
    have hm : ((p : ℤ) % ((7:ℕ):ℤ)) = 1 := by norm_num [p]
    have h7c : ((7:ℕ):ℤ) = (7:ℤ) := by norm_num
    rw [h7c] at hqr
    rw [hqr, legendreSym.mod 7 (p : ℤ), hm, legendreSym.at_one]
  have h := (legendreSym.eq_neg_one_iff (p := p) (a := 7)).mp h7
  exact_mod_cast h

theorem curve_x_ne_zero {x y : Fp} (h : curve.toAffine.Nonsingular x y) : x ≠ 0 := by
  intro hx
  subst hx
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [curve, curveA, curveB, Nat.cast_ofNat, mul_zero, zero_mul, add_zero, zero_add] at heq
  apply seven_not_square
  refine ⟨y, ?_⟩
  have e : (0 : Fp) ^ 3 = 0 := by ring
  rw [e, zero_add] at heq
  rw [← heq]
  ring

theorem pointFinite_eq_x (R : Point) : pointFinite R = decide (pointX R ≠ 0) := by
  cases R with
  | zero => simp [pointFinite, pointX, coordinates]
  | @some x y h =>
    have hx := curve_x_ne_zero h
    have hv : x.val ≠ 0 := by
      intro hz; apply hx; exact (ZMod.val_eq_zero x).mp hz
    simp [pointFinite, pointX, coordinates, hv]

end Curve

section Transfer
attribute [local irreducible] run laneKernel

private theorem reg_map_agree3 (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

private theorem divisor_sites3 : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))
private theorem numerator_sites3 : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))
private theorem control_site3 : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

/-- Transfer of the strong contract of a kernel that needs no zero repair. -/
theorem kernelTransfer_core (L : ControlledPointLayout) (f : Wire → Wire)
    (domain : Finset Wire) (divide : Bool)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 → q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool)
    (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain)
    (bSite : base 2400∈domain)
    (X : Nat) (Y : Fp) (B : Bool)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hX : regValue L.point.x s.basis=X) (hY : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (P : Program) (programSites : wires P⊆domain)
    (P_spec : ∀(t : State)(records : List Bool),
      SkywalkArithmeticInput base X Y.val t.basis →
      t.basis (base 2409)=false → t.basis (base 2410)=false →
      DirectSkywalkArithmeticStrong divide base (base 2400) X Y t (run P records t)) :
    let out := run (renameProgram f P) m s
    out.phase=s.phase ∧ regValue L.point.y out.basis=(directSkywalkResult divide B X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let t := MappedCompressed.LaneA.laneLogicalInput domain f s
  have inputBits (q : Wire) (hq : q∈domain) : t.basis q=s.basis (f q) := by
    simp only [t,MappedCompressed.LaneA.laneLogicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : t.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val t.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) t.basis=X
      rw [reg_map_agree3 f _ t.basis s.basis (fun q hq => inputBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hX
    · change regValue (wireBlock base 2056 256) t.basis=Y.val
      rw [reg_map_agree3 f _ t.basis s.basis (fun q hq => inputBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hY
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [t,MappedCompressed.LaneA.laneLogicalInput,if_neg used]
  have control : t.basis (base 2400)=B := by
    rw [inputBits _ bSite,controlMap,hb]
  have strong := P_spec t m input (zero _ selectorG) (zero _ selectorS)
  have transfer := run_rename_pool f domain injective
    P programSites m t s rfl inputBits
  unfold DirectSkywalkArithmeticStrong at strong
  rw [control] at strong
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (reg_map_agree3 f _ (run P m t).basis
      (run (renameProgram f P) m s).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q outside
    by_cases image : q∈domain.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp image
      have away : a∉skywalkArithmeticNumerator base := by
        intro mem
        apply outside
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨a,mem,rfl⟩
      exact (transfer.2 a ha).trans ((strong.2.2 a away).trans (inputBits a ha))
    · exact run_rename_pool_outside f domain P
        programSites m s q image

private theorem logical_shared_nodup3 : (skywalkSharedWires base).Nodup := by
  apply List.Nodup.map_on
  · intro a _ b _ eq; exact base_injective eq
  · exact List.nodup_range'

private theorem logical_scalar_outside3 (i : Nat) (hi : 2314 ≤ i) :
    base i ∉ skywalkSharedWires base := by
  intro member
  obtain ⟨j,hj,eq⟩ := List.mem_map.mp member
  simp only [List.mem_range'_1] at hj
  have same := base_injective eq
  omega

private theorem logical_selectors_outside3 :
    ∀ q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base := by
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  all_goals exact logical_scalar_outside3 _ (by omega)

private theorem logical_mixed_layout3 :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base) := by
  have scalar : [base 2400,base 2409,base 2410].Nodup := by simp [base]
  have disjoint : [base 2400,base 2409,base 2410].Disjoint (skywalkSharedWires base) :=
    List.disjoint_left.mpr (fun q hq => logical_selectors_outside3 q hq)
  have hall := List.nodup_append'.mpr ⟨scalar,logical_shared_nodup3,disjoint⟩
  have unused : skywalkSharedUnused base⊆skywalkSharedWires base := by
    intro q hq
    simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    all_goals exact arith_mem base 0 2314 _ (by omega) (by omega)
  apply mixedTranscriptTape_layout
  intro r hr
  have pair := (List.nodup_cons.mp (skywalkShared_tape_layout base logical_shared_nodup3
    (base 2400) (logical_selectors_outside3 _ (by simp)) r hr)).2
  have sub : (r.2::r.1::(skywalkSharedField base).wires)⊆skywalkSharedWires base := by
    intro q hq
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).2
    rcases List.mem_cons.mp hq with eq|hq
    · subst q; exact (retained_tape_subset_shared base r hr).1
    · exact retained_field_subset_shared base hq
  constructor
  · exact logical_shared_nodup3
  · apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hall q
    have hp := List.nodup_iff_count.mp pair q
    have hle : (r.2::r.1::(skywalkSharedField base).wires).count q≤
        (skywalkSharedWires base).count q := by
      by_cases hm : q∈r.2::r.1::(skywalkSharedField base).wires
      · have positive := List.count_pos_iff.mpr (sub hm); omega
      · rw [List.count_eq_zero.mpr hm]; omega
    simp only [List.count_append,List.count_cons,List.count_nil] at hh hp hle ⊢
    omega
  · exact fun h => logical_selectors_outside3 _ (by simp) (fusedSharedSites_subset base h)
  · exact fun h => logical_selectors_outside3 _ (by simp) (unused h)
  · exact fun h => logical_selectors_outside3 _ (by simp) (unused h)

end Transfer

section Arith3
attribute [local irreducible] run laneKernel toffoliCount measurementCount

/-- The relabelled lane kernel without the compare-based zero repair. -/
def arith3 (L : ControlledPointLayout) (multiply : Bool) : Program :=
  renameProgram (wireFn2 L) (laneKernel (!multiply))

theorem arith3_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (multiply : Bool) (X Y : Nat) (B : Bool)
    (hX : X<p) (hX0 : 0<X) (hY : Y<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    let V := if B then (if multiply then ((Y:Fp)*(X:Fp)).val else ((Y:Fp)/(X:Fp)).val) else Y
    (run (arith3 L multiply) m s).phase=s.phase ∧
    regValue L.point.y (run (arith3 L multiply) m s).basis=V ∧
    ∀ q,q∉L.point.y → (run (arith3 L multiply) m s).basis q=s.basis q := by
  have yValue : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hY
  rcases placement2 L hw hn with ⟨injective,divisorMap,numeratorMap,controlMap,sharedWork,selectorG,selectorS,_⟩
  have result := kernelTransfer_core L (wireFn2 L) slots.toFinset (!multiply) injective divisorMap
    numeratorMap controlMap sharedWork selectorG selectorS divisor_sites3 numerator_sites3 control_site3
    X (Y:Fp) B s m hb hx (hy.trans yValue.symm) hc
    (laneKernel (!multiply)) (laneKernel_support (!multiply))
    (fun t records input hg hs => NativeFirstDirect.LaneA.laneKernel_spec (!multiply)
      logical_shared_nodup3 base_above logical_selectors_outside3 logical_mixed_layout3
      X (Y:Fp) hX0 hX t records input hg hs)
  cases B <;> cases multiply <;>
    simpa only [arith3,directSkywalkResult,skywalkArithmeticResult,
      Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,yValue] using result

theorem arith3_counts (L : ControlledPointLayout) :
    toffoliCount (arith3 L false)=1051202 ∧ measurementCount (arith3 L false)=721988 ∧
    toffoliCount (arith3 L true)=1051712 ∧ measurementCount (arith3 L true)=721988 := by
  have h1 := laneKernel_counts true
  have h2 := laneKernel_counts false
  have r1 := renameProgram_counts (wireFn2 L) (laneKernel true)
  have r2 := renameProgram_counts (wireFn2 L) (laneKernel false)
  simp only [if_true, Bool.false_eq_true, if_false] at h1 h2
  simp only [arith3, Bool.not_false, Bool.not_true]
  omega

theorem arith3_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (multiply : Bool) : GatePhysical (arith3 L multiply) := by
  apply gatePhysical_rename_support (wireFn2 L) (laneKernel (!multiply))
  · intro a ha b hb eq
    exact (placement2 L hw hn).injectiveOnSlots a (laneKernel_support (!multiply) ha) b
      (laneKernel_support (!multiply) hb) eq
  · exact laneKernel_physical _

theorem arith3_wire (L : ControlledPointLayout) (multiply : Bool) (q : Wire)
    (hq : q ∈ wires (arith3 L multiply)) :
    ∃ old ∈ slots.toFinset, goodW old ∧ q = pointWireFn L (swap2 old) := by
  rw [arith3, renameProgram_support] at hq
  obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨old, laneKernel_support (!multiply) used, laneKernel_avoid (!multiply) old used, rfl⟩

theorem arith3_gateSlots_le (L : ControlledPointLayout) (multiply : Bool) :
    Challenge.gateSlots (arith3 L multiply) ≤ 20500000 := by
  simpa only [arith3, Baselines.rename_gateSlots] using laneKernel_gateSlots_le (!multiply)

end Arith3

section Fix

/-- Low divisor wire. -/
def x0 (L : ControlledPointLayout) : Wire := L.point.x.headD 0

/-- `x₀ ^= ¬finite` on the physical point register. -/
def pfix (L : ControlledPointLayout) : Program :=
  [.X L.point.finite, .CX L.point.finite (x0 L), .X L.point.finite]

def farith (L : ControlledPointLayout) (multiply : Bool) : Program :=
  pfix L ++ (arith3 L multiply ++ pfix L)

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

theorem x_cons (hw : L.Widths) : L.point.x = x0 L :: L.point.x.tail := by
  have h : L.point.x.length = 256 := hw.inputX
  unfold x0
  cases hx : L.point.x with
  | nil => rw [hx] at h; simp at h
  | cons a t => rfl

theorem finite_not_x (hn : L.wires.Nodup) : L.point.finite ∉ L.point.x ++ L.point.y := by
  intro hh
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
  have ht := List.count_pos_iff.mpr hh
  simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
    beq_self_eq_true,if_true] at h ht
  omega

theorem x0_mem (hw : L.Widths) : x0 L ∈ L.point.x := by
  rw [x_cons L hw]; exact List.mem_cons_self ..

theorem finite_ne_x0 (hw : L.Widths) (hn : L.wires.Nodup) : L.point.finite ≠ x0 L := by
  intro h
  exact finite_not_x L hn (List.mem_append_left _ (h ▸ x0_mem L hw))

theorem pfix_run (hw : L.Widths) (hn : L.wires.Nodup) (s : State) (m : List Bool) :
    run (pfix L) m s = ⟨s.phase, writeBit s.basis (x0 L)
      (s.basis (x0 L) ^^ !s.basis L.point.finite)⟩ := by
  have ne := finite_ne_x0 L hw hn
  simp only [pfix, run]
  congr 1
  funext q
  by_cases h1 : q = L.point.finite
  · subst q; simp [writeBit, Function.update, ne]
  · by_cases h2 : q = x0 L
    · subst q; simp [writeBit, Function.update, Ne.symm ne]
    · simp [writeBit, Function.update, h1, h2]

theorem pfix_phase (hw : L.Widths) (hn : L.wires.Nodup) (s : State) (m : List Bool) :
    (run (pfix L) m s).phase = s.phase := by
  rw [pfix_run L hw hn]

theorem pfix_basis (hw : L.Widths) (hn : L.wires.Nodup) (s : State) (m : List Bool) (q : Wire) :
    (run (pfix L) m s).basis q =
      if q = x0 L then (s.basis q ^^ !s.basis L.point.finite) else s.basis q := by
  rw [pfix_run L hw hn]
  show writeBit s.basis (x0 L) _ q = _
  by_cases h : q = x0 L
  · subst h; simp [writeBit]
  · simp [writeBit, Function.update, h]

/-- The flipped divisor value. -/
theorem pfix_value (hw : L.Widths) (hn : L.wires.Nodup) (s : State) (m : List Bool) (X : Nat)
    (hx : regValue L.point.x s.basis = X) (hf : s.basis L.point.finite = decide (X ≠ 0)) :
    regValue L.point.x (run (pfix L) m s).basis = directDivisor X := by
  have hnd : (L.point.x).Nodup := by
    have h := L.dialogUsed_nodup hn
    simp only [dialogUsedWires, PointAddLayout.pointWires, List.cons_append, List.append_assoc] at h
    exact ((List.nodup_cons.mp h).2.sublist (List.sublist_append_left _ _))
  have hx0 := x_cons L hw
  have tailNot : x0 L ∉ L.point.x.tail := by
    have := hnd; rw [hx0] at this; exact (List.nodup_cons.mp this).1
  have tail : regValue L.point.x.tail (run (pfix L) m s).basis = regValue L.point.x.tail s.basis := by
    apply regValue_congr
    intro q hq
    have ne : q ≠ x0 L := fun e => tailNot (e ▸ hq)
    rw [pfix_basis L hw hn, if_neg ne]
  rw [hx0] at hx ⊢
  change (if (run (pfix L) m s).basis (x0 L) then 1 else 0) +
    2 * regValue L.point.x.tail (run (pfix L) m s).basis = _
  change (if s.basis (x0 L) then 1 else 0) + 2 * regValue L.point.x.tail s.basis = X at hx
  rw [tail, pfix_basis L hw hn, if_pos rfl, hf]
  clear tail hx0 hnd tailNot
  by_cases hz : X = 0
  · subst hz
    have h0 : s.basis (x0 L) = false := by
      by_contra hne
      have ht : s.basis (x0 L) = true := by simpa using hne
      rw [ht] at hx; simp at hx
    have h1 : regValue L.point.x.tail s.basis = 0 := by
      rw [h0] at hx; simpa using hx
    rw [h0, h1]
    simp [directDivisor]
  · have hd : decide (X ≠ 0) = true := decide_eq_true hz
    rw [hd, Bool.not_true, Bool.xor_false, show directDivisor X = X from if_neg hz]
    exact hx

section Step
include hw hn
attribute [local irreducible] arith3

/-- Dialog-level arithmetic step, with the finite flag as the zero witness. -/
theorem farith_step (X Y : Fp) (G : Bool) (base : BasisState) (multiply : Bool) (hX : G=true → X≠0)
    (hfin : base L.point.finite = decide (X.val ≠ 0)) :
    Triple (PointDialogValues L X Y G base) (farith L multiply)
      (PointDialogValues L X (if G then (if multiply then Y*X else Y/X) else Y) G base) := by
  intro s m v
  have hfx := finite_not_x L hn
  have hfs : s.basis L.point.finite = decide (X.val ≠ 0) := (v.rest _ hfx).trans hfin
  have x0x := x0_mem L hw
  have x0y : x0 L ∉ L.point.y := by
    intro h
    have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) (x0 L)
    have a := List.count_pos_iff.mpr x0x
    have b := List.count_pos_iff.mpr h
    simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons] at hh
    omega
  have x0pool : x0 L ∉ L.dialogPool := by
    intro h
    have dis := (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
    exact List.disjoint_left.mp dis (by simp [PointAddLayout.pointWires, x0x]) h
  have x0gen : x0 L ≠ L.core.generic := by
    intro h
    have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
    have a := List.count_pos_iff.mpr (h ▸ x0x)
    simp only [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.count_append,List.count_cons,
      beq_self_eq_true,if_true] at hh
    omega
  let D := directDivisor X.val
  have Dpos : 0 < D := Nat.pos_of_ne_zero (directDivisor_ne_zero X.val)
  have Dlt : D < p := by
    by_cases zero : X.val = 0
    · simp only [D,directDivisor,zero,if_true]; norm_num [p]
    · simpa only [D,directDivisor,zero,if_false] using X.isLt
  -- first fix
  obtain ⟨s1, hs1⟩ : ∃ t : State, t = run (pfix L) [] s := ⟨_, rfl⟩
  have s1phase : s1.phase = s.phase := by rw [hs1]; exact pfix_phase L hw hn s _
  have s1q (q : Wire) (hq : q ≠ x0 L) : s1.basis q = s.basis q := by
    rw [hs1, pfix_basis L hw hn, if_neg hq]
  have s1x : regValue L.point.x s1.basis = D := by rw [hs1]; exact pfix_value L hw hn s _ X.val v.x hfs
  have s1y : regValue L.point.y s1.basis = Y.val :=
    (regValue_congr _ _ _ (fun q hq => s1q q (fun e => x0y (e ▸ hq)))).trans v.y
  have s1g : s1.basis L.core.generic = G := (s1q _ (Ne.symm x0gen)).trans v.generic
  have s1c : regValue L.dialogPool s1.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => s1q q (fun e => x0pool (e ▸ hq)))).trans v.clean
  -- kernel
  obtain ⟨s2, hs2⟩ : ∃ t : State,
      t = run (arith3 L multiply) (m.take (measurementCount (arith3 L multiply))) s1 := ⟨_, rfl⟩
  obtain ⟨kp, ky, kf⟩ := arith3_correct L hw hn multiply D Y.val G Dlt Dpos Y.isLt s1
    (m.take (measurementCount (arith3 L multiply))) s1g s1x s1y s1c
  rw [← hs2] at kp ky kf
  have hrun : run (farith L multiply) m s =
      run (pfix L) (m.drop (measurementCount (arith3 L multiply))) s2 := by
    have h0 : measurementCount (pfix L) = 0 := rfl
    simp only [farith, run_append, h0, List.take_zero, List.drop_zero]
    rw [← hs1, ← hs2]
  rw [hrun]
  have s2fin : s2.basis L.point.finite = s.basis L.point.finite :=
    (kf _ (fun h => hfx (List.mem_append_right _ h))).trans (s1q _ (finite_ne_x0 L hw hn))
  have s2x0 : s2.basis (x0 L) = s1.basis (x0 L) := kf _ x0y
  have s1x0 : s1.basis (x0 L) = (s.basis (x0 L) ^^ !s.basis L.point.finite) := by
    rw [hs1, pfix_basis L hw hn, if_pos rfl]
  have hfinal (q : Wire) (hq : q ∉ L.point.y) :
      (run (pfix L) (m.drop (measurementCount (arith3 L multiply))) s2).basis q = s.basis q := by
    rw [pfix_basis L hw hn]
    by_cases h0 : q = x0 L
    · subst q
      rw [if_pos rfl, s2x0, s2fin, s1x0]
      cases s.basis (x0 L) <;> cases s.basis L.point.finite <;> rfl
    · rw [if_neg h0]
      exact (kf q hq).trans (s1q q h0)
  have Dx : G = true → ((D : Nat) : Fp) = X := by
    intro hg
    have hne : X.val ≠ 0 := fun hz => hX hg ((ZMod.val_eq_zero X).mp hz)
    simp only [D, directDivisor, hne, if_false, ZMod.natCast_zmod_val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pfix_phase L hw hn, kp, s1phase]
  · rw [← v.x]
    apply regValue_congr
    intro q hq
    exact hfinal q (fun hy => by
      have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
      have a := List.count_pos_iff.mpr hq
      have b := List.count_pos_iff.mpr hy
      simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons] at hh
      omega)
  · have hy' : regValue L.point.y (run (pfix L) (m.drop (measurementCount (arith3 L multiply))) s2).basis =
        regValue L.point.y s2.basis := by
      apply regValue_congr
      intro q hq
      have ne : q ≠ x0 L := fun e => x0y (by rw [← e]; exact hq)
      rw [pfix_basis L hw hn, if_neg ne]
    rw [hy', ky]
    cases G <;> cases multiply
    · simp
    · simp
    · simp only [if_true, Bool.false_eq_true, if_false]
      rw [Dx rfl, ZMod.natCast_zmod_val]
    · simp only [if_true]
      rw [Dx rfl, ZMod.natCast_zmod_val]
  · exact (hfinal _ (fun h => by
      have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.core.generic
      have b := List.count_pos_iff.mpr h
      simp only [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.count_append,List.count_cons,
        beq_self_eq_true,if_true] at hh
      omega)).trans v.generic
  · rw [← v.clean]
    apply regValue_congr
    intro q hq
    exact hfinal q (fun hy => by
      have dis := (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
      exact List.disjoint_left.mp dis (by simp [PointAddLayout.pointWires, hy]) hq)
  · intro q hq
    have hy : q ∉ L.point.y := fun h => hq (List.mem_append_right _ h)
    exact (hfinal q hy).trans (v.rest q hq)

end Step

end Fix

end ECDSAAdd.Entrant
