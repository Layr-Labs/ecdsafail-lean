import ECDSAAdd.Submission.Entrant.ShortEqual

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paired point comparison against `C` and `-C`.

`C` and `-C` share the finite flag and the abscissa, and (by `shortCode_eq_iff`)
the low bit of `y` then decides which of the two a valid point equals.  The
256-wire abscissa test is computed once by the zero-detection AND chain,
both targets read the chain output together with the low `y` bit, and only then
is the chain erased by measurement.  Each target costs one Toffoli instead of a
separate 258-Toffoli comparison. -/
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout Challenge Baselines RecordedQuantum

/-- The two chain steps of `ZeroControl` (`t := c ∧ ¬a`, and its measured erase). -/
def chainAnd (c a t : Wire) : Program := [.X a, .CCX c a t, .X a]

def chainErase (c a t : Wire) : Program :=
  [.X a, .measureX t [] [.CZ c a], .X a]

theorem chainAnd_run (c a t : Wire) (hca : c≠a) (hat : a≠t)
    (s : State) (m : List Bool) :
    run (chainAnd c a t) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && !s.basis a))⟩ := by
  simp only [chainAnd, run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=a
  · subst w; simp [writeBit, hca, hat]
  · by_cases ht : w=t
    · subst w; simp [writeBit, hca, Ne.symm hat]
    · simp [writeBit, hw, ht, hca]

theorem chainErase_run (c a t : Wire) (hca : c≠a) (hat : a≠t)
    (hct : c≠t) (s : State) (m : List Bool)
    (hq : s.basis t = (s.basis c && !s.basis a)) :
    run (chainErase c a t) m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  simp only [chainErase, run]
  cases hm : m.headD false <;>
    simp [measureAndCorrect, correct, writeBit, hca, hat, hat.symm, hct, hq]
  all_goals
    funext w
    by_cases hw : w=a
    · subst w; simp [hat]
    · simp [Function.update_apply, hw]

/-- `t ^= w ∧ (y = a)`. -/
def bitTest (w y t : Wire) (a : Bool) : Program :=
  if a then [.CCX w y t] else zeroFlag y w t

theorem bitTest_run (w y t : Wire) (a : Bool) (hwy : w≠y) (hyt : y≠t) (hwt : w≠t)
    (s : State) (m : List Bool) :
    run (bitTest w y t a) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis w && (s.basis y == a)))⟩ := by
  cases a with
  | false =>
    simp only [bitTest, Bool.false_eq_true, if_false]
    rw [zeroFlag_run y w t hwy hyt s m]
    cases s.basis y <;> rfl
  | true =>
    simp only [bitTest, if_true, run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq : q=t
    · subst q; cases s.basis y <;> simp [writeBit]
    · simp [writeBit, hq]

/-- Both enabled targets read the chain output `w` and the low `y` bit. -/
def pairTail (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire) : Program :=
  (if e₁ then bitTest w y t₁ a₁ else []) ++ (if e₂ then bitTest w y t₂ a₂ else [])

def pairEffect (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (v : Bool) (s : BasisState) : BasisState :=
  writeBit (writeBit s t₁ (s t₁ ^^ (e₁ && v && (s y == a₁)))) t₂
    (s t₂ ^^ (e₂ && v && (s y == a₂)))

theorem pairTail_counts (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire) :
    toffoliCount (pairTail y t₁ t₂ e₁ a₁ e₂ a₂ w) = e₁.toNat + e₂.toNat ∧
    measurementCount (pairTail y t₁ t₂ e₁ a₁ e₂ a₂ w) = 0 := by
  cases e₁ <;> cases e₂ <;> cases a₁ <;> cases a₂ <;>
    simp [pairTail, bitTest, zeroFlag, toffoliCount, measurementCount]

theorem pairTail_run (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire)
    (hwy : w≠y) (hw1 : w≠t₁) (hw2 : w≠t₂) (hy1 : y≠t₁) (hy2 : y≠t₂) (h12 : t₁≠t₂)
    (s : State) (m : List Bool) :
    run (pairTail y t₁ t₂ e₁ a₁ e₂ a₂ w) m s =
      ⟨s.phase, pairEffect y t₁ t₂ e₁ a₁ e₂ a₂ (s.basis w) s.basis⟩ := by
  have hfirst : run (if e₁ then bitTest w y t₁ a₁ else []) m s =
      ⟨s.phase, writeBit s.basis t₁ (s.basis t₁ ^^ (e₁ && s.basis w && (s.basis y == a₁)))⟩ := by
    cases e₁
    · simp only [Bool.false_eq_true, if_false, run, Bool.false_and, Bool.xor_false]
      cases s; simp [writeBit]
    · simp only [if_true, Bool.true_and]
      exact bitTest_run w y t₁ a₁ hwy hy1 hw1 s m
  have hm1 : measurementCount (if e₁ then bitTest w y t₁ a₁ else []) = 0 := by
    cases e₁ <;> cases a₁ <;> simp [bitTest, zeroFlag, measurementCount]
  rw [pairTail, run_append, run_take, hfirst, hm1, List.drop_zero]
  cases e₂
  · simp only [Bool.false_eq_true, if_false, run]
    congr 1
    funext q
    simp only [pairEffect, writeBit, Function.update_apply, Bool.false_and, Bool.xor_false]
    by_cases hq2 : q = t₂
    · subst hq2; simp [Ne.symm h12]
    · simp [hq2]
  · simp only [if_true]
    rw [bitTest_run w y t₂ a₂ hwy hy2 hw2]
    congr 1
    funext q
    simp only [pairEffect, writeBit, Function.update_apply, Bool.true_and]
    by_cases hq2 : q=t₂
    · subst q; simp [Ne.symm h12, Ne.symm hw1, hy1.symm, hw1, hy1]
    · by_cases hq1 : q=t₁
      · subst q; simp [h12, hw1, hy1]
      · simp [hq1, hq2]

/-- Zero chain whose innermost step is `T` applied to the chain output. -/
def zeroWith (T : Wire → Program) (c : Wire) : List ZeroBit → Program
  | [] => T c
  | b::bs => chainAnd c b.input b.work ++ zeroWith T b.work bs ++ chainErase c b.input b.work

theorem zeroWith_counts (T : Wire → Program) (n : Nat)
    (hT : ∀ w, toffoliCount (T w) = n ∧ measurementCount (T w) = 0) (c : Wire) (bs : List ZeroBit) :
    toffoliCount (zeroWith T c bs) = bs.length + n ∧
    measurementCount (zeroWith T c bs) = bs.length := by
  induction bs generalizing c with
  | nil => simpa [zeroWith] using hT c
  | cons b bs ih =>
    have h := ih b.work
    simp only [zeroWith, chainAnd, chainErase, toffoliCount_append, measurementCount_append,
      List.length_cons]
    simp [toffoliCount, measurementCount] at h ⊢
    omega

theorem zeroWith_pair_run (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (c : Wire) (bs : List ZeroBit)
    (hnd : (c::y::t₁::t₂::bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (m : List Bool) (hz : ∀ b∈bs, s.basis b.work=false) :
    run (zeroWith (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) c bs) m s =
      ⟨s.phase, pairEffect y t₁ t₂ e₁ a₁ e₂ a₂
        (s.basis c && bs.all (fun b => !s.basis b.input)) s.basis⟩ := by
  induction bs generalizing c s m with
  | nil =>
    have hni := hnd
    simp only [List.flatMap_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      or_false] at hni
    obtain ⟨⟨hcy, hc1, hc2⟩, ⟨hy1, hy2⟩, h12, -⟩ := hni
    simp only [zeroWith, List.all_nil, Bool.and_true]
    exact pairTail_run y t₁ t₂ e₁ a₁ e₂ a₂ c hcy hc1 hc2 hy1 hy2 h12 s m
  | cons b bs ih =>
    have hnames : (c::y::t₁::t₂::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hnd
    have hni := hnames
    simp only [List.nodup_cons, List.mem_cons, not_or] at hni
    obtain ⟨⟨hcy, hc1, hc2, hci, hcw, hcR⟩, ⟨hy1, hy2, hyi, hyw, hyR⟩, ⟨h12, h1i, h1w, h1R⟩,
      ⟨h2i, h2w, h2R⟩, ⟨hiw, hiR⟩, hwR, hR⟩ := hni
    have hchild : (b.work::y::t₁::t₂::bs.flatMap ZeroBit.wires).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨Ne.symm hyw, Ne.symm h1w, Ne.symm h2w, hwR⟩, ⟨hy1, hy2, hyR⟩, ⟨h12, h1R⟩, h2R, hR⟩
    let q := s.basis c && !s.basis b.input
    let t : State := ⟨s.phase, writeBit s.basis b.work q⟩
    have hp : run (chainAnd c b.input b.work) m s=t := by
      rw [chainAnd_run c b.input b.work hci hiw]
      simp [t, q, hz b (by simp), writeBit]
    have htail (d : ZeroBit) (hd : d∈bs) : d.work≠b.work ∧ d.input≠b.work := by
      constructor <;> intro he <;> apply hwR <;>
        apply List.mem_flatMap.mpr <;> refine ⟨d,hd,?_⟩ <;> simp [ZeroBit.wires, he]
    have hz' : ∀ d∈bs, t.basis d.work=false := by
      intro d hd
      simpa [t, writeBit, (htail d hd).1] using hz d (by simp [hd])
    have hall : bs.all (fun d => !t.basis d.input) = bs.all (fun d => !s.basis d.input) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor <;> intro h d hd <;> simpa [t, writeBit, (htail d hd).2] using h d hd
    have hcnt := (zeroWith_counts (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) (e₁.toNat + e₂.toNat)
      (pairTail_counts y t₁ t₂ e₁ a₁ e₂ a₂) b.work bs).2
    change run (chainAnd c b.input b.work ++ zeroWith (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) b.work bs ++
      chainErase c b.input b.work) m s = _
    rw [run_append, run_take, run_append, run_take]
    simp only [measurementCount_append, hcnt,
      show measurementCount (chainAnd c b.input b.work)=0 from rfl, Nat.zero_add, List.drop_zero]
    rw [hp, ih b.work hchild t m hz']
    rw [chainErase_run c b.input b.work hci hiw hcw _ _ (by
      simp only [pairEffect, t, writeBit, Function.update_apply]
      simp [Ne.symm h1w, Ne.symm h2w, hcw, hc1, hc2, hiw, Ne.symm h1i, Ne.symm h2i, q])]
    simp only [hall, List.all_cons]
    apply congrArg (State.mk s.phase)
    funext w
    simp only [pairEffect, writeBit, Function.update_apply]
    by_cases hw2 : w=t₂
    · subst w
      simp [h2w, Ne.symm h12, hyw, t, q, writeBit, Function.update_apply, Bool.and_assoc]
    · by_cases hw1 : w=t₁
      · subst w
        simp [hw2, h1w, hyw, t, q, writeBit, Function.update_apply, Bool.and_assoc]
      · by_cases hww : w=b.work
        · subst w
          simp [hw1, hw2, hz b (by simp)]
        · simp [hww, hw1, hw2, t, writeBit, Function.update_apply]


/-! ### Layout instance -/

/-- The abscissa (shared by `C` and `-C`); it also decides finiteness, see `finite_of_x_eq`. -/
def pairSrc (L : ControlledPointLayout) : List Wire := L.point.x

def pairCode (R : Point) : Nat := pointX R

def pairPorts (L : ControlledPointLayout) : List ZeroBit :=
  zeroPorts (pairSrc L) (L.dialogPool.take 256)

/-- The low bit of the in-place `y` register. -/
def yLow (L : ControlledPointLayout) : Wire := L.point.y.headD L.control

def yBit (R : Point) : Bool := decide (pointY R % 2 = 1)

/-- `t₁ ^= e₁ ∧ control ∧ point = C` and `t₂ ^= e₂ ∧ control ∧ point = D`, where `D`
must share the flag/abscissa code of `C` (used with `D = -C`). -/
def pairEqual (L : ControlledPointLayout) (t₁ t₂ : Wire) (e₁ e₂ : Bool) (C D : Point) : Program :=
  xorConstant (pairSrc L) (pairCode C) ++
  zeroWith (pairTail (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) L.control (pairPorts L) ++
  xorConstant (pairSrc L) (pairCode C)

theorem pairCode_lt (R : Point) : pairCode R < 2^256 := by
  have hp : p < 2^256 := by norm_num [p]
  have hx := (point_coordinates_lt R).1
  unfold pairCode
  omega

theorem pairCode_neg (C : Point) : pairCode (-C) = pairCode C := by
  cases C with
  | zero => rfl
  | @some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    rfl

theorem shortCode_pair (R : Point) : shortCodeX R = pairCode R + 2^256 * (pointY R % 2) := by
  unfold shortCodeX pairCode
  ring

theorem pair_value_eq (R C : Point) :
    (decide (pairCode R = pairCode C) && (yBit R == yBit C)) = pointEqual R C := by
  apply Bool.eq_iff_iff.mpr
  rw [pointEqual_true_iff, ← shortCode_eq_iff, ← shortCodeX_eq_iff, shortCode_pair, shortCode_pair]
  have h1 := pairCode_lt R
  have h2 := pairCode_lt C
  have hyR : pointY R % 2 < 2 := Nat.mod_lt _ (by decide)
  have hyC : pointY C % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, yBit]
  constructor
  · rintro ⟨ha, hb⟩
    rw [ha]
    have : pointY R % 2 = pointY C % 2 := by
      by_cases hr : pointY R % 2 = 1 <;> by_cases hc : pointY C % 2 = 1 <;>
        simp_all <;> omega
    rw [this]
  · intro h
    have ha : pairCode R = pairCode C := by omega
    have hb : pointY R % 2 = pointY C % 2 := by omega
    exact ⟨ha, by rw [hb]⟩

theorem pairSrc_length (L : ControlledPointLayout) (hw : L.Widths) : (pairSrc L).length = 256 := by
  simp [pairSrc, show L.point.x.length = 256 from hw.inputX]

theorem pairWork_length (L : ControlledPointLayout) (hw : L.Widths) :
    (L.dialogPool.take 256).length = 256 := by
  simp [L.dialogPool_length hw]

theorem pairSrc_value (L : ControlledPointLayout) (hw : L.Widths) (R : Point) (s : BasisState)
    (hp : Holds.holds s L.point R) : regValue (pairSrc L) s = pairCode R := by
  have hv := (point_holds L.point R s).mp hp
  exact hv.2.1

theorem yLow_mem (L : ControlledPointLayout) (hw : L.Widths) : yLow L ∈ L.point.y := by
  have hl : L.point.y.length = 256 := hw.inputY
  unfold yLow
  cases hy : L.point.y with
  | nil => rw [hy] at hl; simp at hl
  | cons w ys => simp

theorem yLow_value (L : ControlledPointLayout) (hw : L.Widths) (R : Point) (s : BasisState)
    (hp : Holds.holds s L.point R) : s (yLow L) = yBit R := by
  have hv := (point_holds L.point R s).mp hp
  have hl : L.point.y.length = 256 := hw.inputY
  have hy := hv.2.2
  unfold yLow yBit
  cases hc : L.point.y with
  | nil => rw [hc] at hl; simp at hl
  | cons w ys =>
    rw [hc] at hy
    change (if s w then 1 else 0) + 2 * regValue ys s = pointY R at hy
    simp only [List.headD_cons]
    rw [← hy]
    cases s w <;> simp <;> omega

theorem pair_nodup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (t₁ t₂ : Wire) (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂) :
    (L.control :: yLow L :: t₁ :: t₂ :: (pairSrc L ++ L.dialogPool.take 256)).Nodup := by
  have sep := dialogFlag_separation L hn
  have hc1 : L.control ≠ t₁ := fun h => (List.nodup_cons.mp sep).1 (h ▸ ht1)
  have hc2 : L.control ≠ t₂ := fun h => (List.nodup_cons.mp sep).1 (h ▸ ht2)
  have hA : (L.control :: t₁ :: (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513)).Nodup := by
    simpa only [List.cons_append] using L.dialogPointZero_nodup hn L.control t₁ hc1 (Or.inl rfl) ht1
  have hB : (L.control :: t₂ :: (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513)).Nodup := by
    simpa only [List.cons_append] using L.dialogPointZero_nodup hn L.control t₂ hc2 (Or.inl rfl) ht2
  have a1 := (List.nodup_cons.mp hA).1
  have a2 := (List.nodup_cons.mp (List.nodup_cons.mp hA).2).1
  have b2 := (List.nodup_cons.mp (List.nodup_cons.mp hB).2).1
  have hPP := (List.nodup_cons.mp (List.nodup_cons.mp hA).2).2
  have hsub : (pairSrc L ++ L.dialogPool.take 256).Sublist
      (PointAddLayout.pointWires L.point ++ L.dialogPool.take 513) := by
    have h1 : (pairSrc L).Sublist (PointAddLayout.pointWires L.point) := by
      simp only [pairSrc, PointAddLayout.pointWires, List.cons_append]
      exact (List.sublist_append_left L.point.x L.point.y).trans (List.sublist_cons_self _ _)
    have h2 : (L.dialogPool.take 256).Sublist (L.dialogPool.take 513) := by
      have he : L.dialogPool.take 256 = (L.dialogPool.take 513).take 256 := by
        rw [List.take_take]; rfl
      rw [he]; exact List.take_sublist _ _
    exact h1.append h2
  have sub := hsub.subset
  have hyPW : yLow L ∈ PointAddLayout.pointWires L.point := by
    simp [PointAddLayout.pointWires, yLow_mem L hw]
  have hyP : yLow L ∈ PointAddLayout.pointWires L.point ++ L.dialogPool.take 513 :=
    List.mem_append.mpr (Or.inl hyPW)
  have hPWnd := (List.nodup_append.mp hPP)
  have hy_notsrc : yLow L ∉ pairSrc L := by
    intro h
    have hnd : (pairSrc L ++ L.point.y).Nodup := by
      have h0 := hPWnd.1
      simp only [PointAddLayout.pointWires, List.cons_append] at h0
      exact (List.nodup_cons.mp h0).2
    exact (List.nodup_append.mp hnd).2.2 _ h _ (yLow_mem L hw) rfl
  have h2' : (L.dialogPool.take 256).Sublist (L.dialogPool.take 513) := by
    have he : L.dialogPool.take 256 = (L.dialogPool.take 513).take 256 := by
      rw [List.take_take]; rfl
    rw [he]; exact List.take_sublist _ _
  have hy_notwork : yLow L ∉ L.dialogPool.take 256 := fun h =>
    hPWnd.2.2 _ hyPW _ (h2'.subset h) rfl
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
    List.nodup_cons.mpr ⟨?_, hPP.sublist hsub⟩⟩⟩⟩
  · intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h
    · exact a1 (List.mem_cons_of_mem _ (h ▸ hyP))
    · exact hc1 h
    · exact hc2 h
    · exact a1 (List.mem_cons_of_mem _ (sub h))
  · intro h
    simp only [List.mem_cons, List.mem_append] at h
    rcases h with h | h | h | h
    · exact a2 (h ▸ hyP)
    · exact b2 (h ▸ hyP)
    · exact hy_notsrc h
    · exact hy_notwork h
  · intro h
    simp only [List.mem_cons] at h
    rcases h with h | h
    · exact h12 h
    · exact a2 (sub h)
  · exact fun h => b2 (sub h)

theorem pairPorts_maps (L : ControlledPointLayout) (hw : L.Widths) :
    (pairPorts L).map ZeroBit.input = pairSrc L ∧
    (pairPorts L).map ZeroBit.work = L.dialogPool.take 256 :=
  zeroPorts_maps _ _ ((pairSrc_length L hw).trans (pairWork_length L hw).symm)

theorem pairPorts_length (L : ControlledPointLayout) (hw : L.Widths) : (pairPorts L).length = 256 := by
  have h := congrArg List.length (pairPorts_maps L hw).1
  simpa only [List.length_map, pairSrc_length L hw] using h

theorem pairEqual_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (t₁ t₂ : Wire) (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂)
    (e₁ e₂ : Bool) (C D R : Point) (s : State) (m : List Bool)
    (hp : Holds.holds s.basis L.point R) (hz : regValue (L.dialogPool.take 256) s.basis = 0) :
    run (pairEqual L t₁ t₂ e₁ e₂ C D) m s =
      ⟨s.phase, pairEffect (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)
        (s.basis L.control && decide (pairCode R = pairCode C)) s.basis⟩ := by
  have hnd := pair_nodup L hw hn t₁ t₂ ht1 ht2 h12
  have hn4 := hnd
  simp only [List.nodup_cons, List.mem_cons, List.mem_append, not_or] at hn4
  obtain ⟨⟨hcy, hc1, hc2, hcs, hcw⟩, ⟨hy1, hy2, hys, hyw⟩, ⟨h12', h1s, h1w⟩, ⟨h2s, h2w⟩, hsw⟩ := hn4
  have hsrc : (pairSrc L).Nodup := (List.nodup_append.mp hsw).1
  have hdisj : ∀ q ∈ L.dialogPool.take 256, q ∉ pairSrc L := by
    intro q hq hs
    exact (List.nodup_append.mp hsw).2.2 q hs q hq rfl
  have hmaps := pairPorts_maps L hw
  have hperm := zeroPorts_perm (pairSrc L) (L.dialogPool.take 256)
    ((pairSrc_length L hw).trans (pairWork_length L hw).symm)
  have hchain : (L.control :: yLow L :: t₁ :: t₂ :: (pairPorts L).flatMap ZeroBit.wires).Nodup :=
    ((((hperm.cons _).cons _).cons _).cons _).nodup_iff.mpr hnd
  have hk : pairCode C < 2^(pairSrc L).length := by
    rw [pairSrc_length L hw]
    exact pairCode_lt C
  have hval : regValue (pairSrc L) s.basis = pairCode R := pairSrc_value L hw R s.basis hp
  obtain ⟨hup, hue, huv⟩ := xorConstant_correct (pairSrc L) hsrc (pairCode C) hk s m
  generalize hu : run (xorConstant (pairSrc L) (pairCode C)) m s = u at hup hue huv
  have hwork (b : ZeroBit) (hb : b ∈ pairPorts L) : b.work ∈ L.dialogPool.take 256 := by
    rw [← hmaps.2]; exact List.mem_map.mpr ⟨b, hb, rfl⟩
  have huz : ∀ b ∈ pairPorts L, u.basis b.work = false := by
    intro b hb
    rw [hue _ (hdisj _ (hwork b hb))]
    exact (regValue_zero _ _).mp hz _ (hwork b hb)
  have hh := zeroWith_pair_run (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D) L.control (pairPorts L)
    hchain u m huz
  have hall : (pairPorts L).all (fun b => !u.basis b.input) =
      decide (regValue (pairSrc L) s.basis = pairCode C) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true]
    simp only [Bool.not_eq_true']
    have heq : (∀ b ∈ pairPorts L, u.basis b.input = false) ↔ regValue (pairSrc L) u.basis = 0 := by
      rw [regValue_zero, ← hmaps.1]
      simp
    rw [heq, huv]
    simp
  have hcu : u.basis L.control = s.basis L.control := hue _ hcs
  rw [hall, hcu, hval] at hh
  have hcnt := (zeroWith_counts (pairTail (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) (e₁.toNat + e₂.toNat)
    (pairTail_counts (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) L.control (pairPorts L)).2
  rw [pairPorts_length L hw] at hcnt
  rw [pairEqual, run_append, run_take, run_append, run_take]
  simp only [measurementCount_append, (xorConstant_counts _ _).2, hcnt, Nat.zero_add, List.drop_zero]
  rw [hu, hh]
  generalize hvdef : (⟨u.phase, pairEffect (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)
    (s.basis L.control && decide (pairCode R = pairCode C)) u.basis⟩ : State) = v
  have hvb : v.basis = pairEffect (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)
      (s.basis L.control && decide (pairCode R = pairCode C)) u.basis := by rw [← hvdef]
  have hvph : v.phase = u.phase := by rw [← hvdef]
  obtain ⟨hvp, hve, hvv⟩ := xorConstant_correct (pairSrc L) hsrc (pairCode C) hk v (m.drop 256)
  have hvs : regValue (pairSrc L) v.basis = regValue (pairSrc L) u.basis := by
    rw [hvb]
    apply regValue_congr
    intro w hw'
    have hw1 : w ≠ t₁ := fun he => h1s (he ▸ hw')
    have hw2 : w ≠ t₂ := fun he => h2s (he ▸ hw')
    simp [pairEffect, writeBit, Function.update_apply, hw1, hw2]
  have hrestore : regValue (pairSrc L) (run (xorConstant (pairSrc L) (pairCode C)) (m.drop 256) v).basis =
      regValue (pairSrc L) s.basis := by
    rw [hvv, hvs, huv, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  apply (show ∀ a b : State, a.phase = b.phase → a.basis = b.basis → a = b from
    fun ⟨ap, ab⟩ ⟨bp, bb⟩ hp hb => by cases hp; cases hb; rfl)
  · rw [hvp, hvph, hup]
  · funext w
    by_cases hw' : w ∈ pairSrc L
    · rw [(regValue_eq_iff (pairSrc L) _ _).mp hrestore w hw']
      have hw1 : w ≠ t₁ := fun he => h1s (he ▸ hw')
      have hw2 : w ≠ t₂ := fun he => h2s (he ▸ hw')
      simp [pairEffect, writeBit, Function.update_apply, hw1, hw2]
    · rw [hve w hw', hvb]
      have hyu : u.basis (yLow L) = s.basis (yLow L) := hue _ hys
      have h1u : u.basis t₁ = s.basis t₁ := hue _ h1s
      have h2u : u.basis t₂ = s.basis t₂ := hue _ h2s
      have hwu : u.basis w = s.basis w := hue _ hw'
      simp only [pairEffect, writeBit, Function.update_apply, hyu, h1u, h2u]
      split_ifs <;> simp [hwu]

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pairBoundary (R C : Point) (b : Bool) (f : BasisState) (t₁ t₂ : Wire)
    (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂)
    (e₁ e₂ B₁ B₂ : Bool) (hB₁ : B₁ = (b && e₁)) (hB₂ : B₂ = (b && e₂)) :
    Triple (PointDialogBoundary L R b f) (pairEqual L t₁ t₂ e₁ e₂ C (-C))
      (PointDialogBoundary L R b (writeBit (writeBit f t₁ (f t₁ ^^ (B₁ && pointEqual R C))) t₂
        (f t₂ ^^ (B₂ && pointEqual R (-C))))) := by
  intro s m v
  have hclean : regValue (L.dialogPool.take 256) s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.take_subset _ _ hq))
  have hh := pairEqual_correct L hw hn t₁ t₂ ht1 ht2 h12 e₁ e₂ C (-C) R s m v.point hclean
  have hy := yLow_value L hw R s.basis v.point
  have hb := v.control
  have k1 : (e₁ && (s.basis L.control && decide (pairCode R = pairCode C)) &&
      (s.basis (yLow L) == yBit C)) = (B₁ && pointEqual R C) := by
    rw [hB₁, hy, hb, ← pair_value_eq R C]
    generalize decide (pairCode R = pairCode C) = d
    generalize (yBit R == yBit C) = g
    cases e₁ <;> cases b <;> cases d <;> cases g <;> rfl
  have k2 : (e₂ && (s.basis L.control && decide (pairCode R = pairCode C)) &&
      (s.basis (yLow L) == yBit (-C))) = (B₂ && pointEqual R (-C)) := by
    rw [hB₂, hy, hb, ← pair_value_eq R (-C), pairCode_neg]
    generalize decide (pairCode R = pairCode C) = d
    generalize (yBit R == yBit (-C)) = g
    cases e₂ <;> cases b <;> cases d <;> cases g <;> rfl
  have hfin : (run (pairEqual L t₁ t₂ e₁ e₂ C (-C)) m s).basis =
      writeBit (writeBit s.basis t₁ (s.basis t₁ ^^ (B₁ && pointEqual R C))) t₂
        (s.basis t₂ ^^ (B₂ && pointEqual R (-C))) := by
    rw [hh]
    simp only [pairEffect]
    rw [k1, k2]
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hfin]
    simp only [writeBit, Function.update_apply]
    by_cases q2 : q = t₂
    · subst q2; simp [v.flags _ ht2]
    · by_cases q1 : q = t₁
      · subst q1; simp [q2, v.flags _ ht1]
      · simp [q1, q2, v.flags q hq]
  · intro q hq
    rw [hfin]
    have q1 : q ≠ t₁ := fun he => hq (he ▸ ht1)
    have q2 : q ≠ t₂ := fun he => hq (he ▸ ht2)
    simp [writeBit, q1, q2]

/-- Input side: `double ^= K ∧ R = C` and `genericSelect ^= b ∧ R = -C`. -/
theorem pairFlag_input (R C : Point) (cy : Fp) (b O D I G E H K : Bool)
    (hK : K = (b && decide (cy ≠ -cy))) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (pairEqual L L.doubleSelect L.genericSelect (decide (cy ≠ -cy)) true C (-C))
      (PointDialogBoundary L R b
        (dialogFlagState L O (D ^^ (K && pointEqual R C)) (I ^^ (b && pointEqual R (-C))) G E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn R C b (dialogFlagState L O D I G E H K) L.doubleSelect L.genericSelect
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    (decide (cy ≠ -cy)) true K b hK (by simp)
  simp only [hr.2.1, hr.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (D ^^ (K && pointEqual R C))).2.1
  have u2 := (dialogFlagState_update L hn O (D ^^ (K && pointEqual R C)) I G E H K
    (I ^^ (b && pointEqual R (-C)))).2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

/-- Output side: `infinitySelect ^= b ∧ S = C` and `equalNegY ^= E ∧ S = -C`. -/
theorem pairFlag_output (S C : Point) (en : Bool) (b O D I G E H K : Bool)
    (hE : E = (b && en)) :
    Triple (PointDialogBoundary L S b (dialogFlagState L O D I G E H K))
      (pairEqual L L.infinitySelect L.core.equalNegY true en C (-C))
      (PointDialogBoundary L S b
        (dialogFlagState L (O ^^ (b && pointEqual S C)) D I G E (H ^^ (E && pointEqual S (-C))) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn S C b (dialogFlagState L O D I G E H K) L.infinitySelect L.core.equalNegY
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    true en b E (by simp) hE
  simp only [hr.1, hr.2.2.2.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (O ^^ (b && pointEqual S C))).1
  have u2 := (dialogFlagState_update L hn (O ^^ (b && pointEqual S C)) D I G E H K
    (H ^^ (E && pointEqual S (-C)))).2.2.2.2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

end

theorem pairEqual_counts (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire) (e₁ e₂ : Bool)
    (C D : Point) :
    toffoliCount (pairEqual L t₁ t₂ e₁ e₂ C D) ≤ 258 ∧
    measurementCount (pairEqual L t₁ t₂ e₁ e₂ C D) = 256 := by
  have h := zeroWith_counts (pairTail (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) (e₁.toNat + e₂.toNat)
    (pairTail_counts (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D)) L.control (pairPorts L)
  rw [pairPorts_length L hw] at h
  have x := xorConstant_counts (pairSrc L) (pairCode C)
  simp only [pairEqual, toffoliCount_append, measurementCount_append, x.1, x.2, h.1, h.2]
  have h1 : e₁.toNat ≤ 1 := by cases e₁ <;> decide
  have h2 : e₂.toNat ≤ 1 := by cases e₂ <;> decide
  refine ⟨?_, ?_⟩
  · omega
  · simp

theorem pairTail_wires (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire) :
    wires (pairTail y t₁ t₂ e₁ a₁ e₂ a₂ w) ⊆ ({w, y, t₁, t₂} : Finset Wire) := by
  intro q hq
  cases e₁ <;> cases e₂ <;> cases a₁ <;> cases a₂ <;>
    simp [pairTail, bitTest, zeroFlag, wires, Instr.wires, wires_append] at hq ⊢ <;> tauto

theorem zeroWith_pair_wires (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (c : Wire) (bs : List ZeroBit) :
    wires (zeroWith (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) c bs) ⊆
      (c :: y :: t₁ :: t₂ :: bs.flatMap ZeroBit.wires).toFinset := by
  induction bs generalizing c with
  | nil =>
    intro q hq
    have := pairTail_wires y t₁ t₂ e₁ a₁ e₂ a₂ c (by simpa [zeroWith] using hq)
    simp at this ⊢; tauto
  | cons b bs ih =>
    intro q hq
    simp only [zeroWith, wires_append, Finset.mem_union] at hq
    have hsub := @ih b.work q
    simp [chainAnd, chainErase, wires, Instr.wires, correctionWires, ZeroBit.wires] at hq hsub ⊢
    rcases hq with ((h | h | h) | h) | (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · rcases hsub h with h' | h' | h' | h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h')))))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem pairEqual_wires (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire) (e₁ e₂ : Bool)
    (C D : Point) :
    wires (pairEqual L t₁ t₂ e₁ e₂ C D) ⊆
      (L.control :: yLow L :: t₁ :: t₂ :: (pairSrc L ++ L.dialogPool.take 256)).toFinset := by
  have hperm := zeroPorts_perm (pairSrc L) (L.dialogPool.take 256)
    ((pairSrc_length L hw).trans (pairWork_length L hw).symm)
  have hx := xorConstant_wires_subset (pairSrc L) (pairCode C)
  have hz := zeroWith_pair_wires (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D) L.control (pairPorts L)
  intro q hq
  simp only [pairEqual, wires_append, Finset.mem_union] at hq
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
  rcases hq with (h | h) | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_toFinset.mp (hx h))))))
  · have h' := hz h
    simp only [List.mem_toFinset, List.mem_cons] at h'
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (List.mem_append.mp (hperm.subset h')))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_toFinset.mp (hx h))))))

theorem pairEqual_sites (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire)
    (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (e₁ e₂ : Bool) (C D : Point) :
    wires (pairEqual L t₁ t₂ e₁ e₂ C D) ⊆ (CompressedPointDialog.sites L).toFinset := by
  intro q hq
  have h := pairEqual_wires L hw t₁ t₂ e₁ e₂ C D hq
  have hy := yLow_mem L hw
  have hpool := CompressedPointDialog.prefix_small L hw 256 (by decide)
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at h
  simp only [CompressedPointDialog.sites, CompressedPointSquare.residents,
    PointAddLayout.pointWires, List.mem_toFinset, List.mem_append, List.mem_cons]
  rcases h with rfl | rfl | rfl | rfl | h | h
  · simp
  · simp [hy]
  · simp [ht1]
  · simp [ht2]
  · simp [h]
  · exact Or.inr (hpool h)

theorem pairEqual_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (t₁ t₂ : Wire) (ht1 : t₁ ∈ L.inPlaceFlags) (ht2 : t₂ ∈ L.inPlaceFlags) (h12 : t₁ ≠ t₂)
    (e₁ e₂ : Bool) (C D : Point) : GatePhysical (pairEqual L t₁ t₂ e₁ e₂ C D) := by
  have hnd := pair_nodup L hw hn t₁ t₂ ht1 ht2 h12
  have hperm := zeroPorts_perm (pairSrc L) (L.dialogPool.take 256)
    ((pairSrc_length L hw).trans (pairWork_length L hw).symm)
  have hchain : (L.control :: yLow L :: t₁ :: t₂ :: (pairPorts L).flatMap ZeroBit.wires).Nodup :=
    ((((hperm.cons _).cons _).cons _).cons _).nodup_iff.mpr hnd
  simp only [pairEqual, gatePhysical_append]
  refine ⟨⟨xorConstant_physical _ _, ?_⟩, xorConstant_physical _ _⟩
  clear hnd hperm
  generalize L.control = c at hchain ⊢
  generalize pairPorts L = bs at hchain ⊢
  generalize yLow L = y at hchain ⊢
  induction bs generalizing c with
  | nil =>
    simp only [List.flatMap_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      or_false] at hchain
    obtain ⟨⟨hcy, hc1, hc2⟩, ⟨hy1, hy2⟩, -, -⟩ := hchain
    simp only [zeroWith]
    cases e₁ <;> cases e₂ <;> cases (yBit C) <;> cases (yBit D) <;>
      simp [pairTail, bitTest, zeroFlag, GatePhysical, PhysicalInstr, ProperGate, gatePhysical_append,
        hc1, hc2, hy1, hy2]
  | cons b bs ih =>
    have hnames : (c::y::t₁::t₂::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hchain
    have hni := hnames
    simp only [List.nodup_cons, List.mem_cons, not_or] at hni
    obtain ⟨⟨hcy, hc1, hc2, hci, hcw, hcR⟩, ⟨hy1, hy2, hyi, hyw, hyR⟩, ⟨h12, h1i, h1w, h1R⟩,
      ⟨h2i, h2w, h2R⟩, ⟨hiw, hiR⟩, hwR, hR⟩ := hni
    have hchild : (b.work::y::t₁::t₂::bs.flatMap ZeroBit.wires).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨Ne.symm hyw, Ne.symm h1w, Ne.symm h2w, hwR⟩, ⟨hy1, hy2, hyR⟩, ⟨h12, h1R⟩, h2R, hR⟩
    simp only [zeroWith, gatePhysical_append]
    exact ⟨⟨by simp [chainAnd, GatePhysical, PhysicalInstr, ProperGate, hcw, hiw], ih b.work hchild⟩,
      by simp [chainErase, GatePhysical, PhysicalInstr, ProperGate]⟩

theorem zeroWith_pair_slots (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (c : Wire) (bs : List ZeroBit) :
    gateSlots (zeroWith (pairTail y t₁ t₂ e₁ a₁ e₂ a₂) c bs) ≤ 7 * bs.length + 6 := by
  induction bs generalizing c with
  | nil =>
    cases e₁ <;> cases e₂ <;> cases a₁ <;> cases a₂ <;>
      simp [zeroWith, pairTail, bitTest, zeroFlag, gateSlots_append, gateSlots_cons, instructionSlots]
  | cons b bs ih =>
    have h := ih b.work
    simp only [zeroWith, chainAnd, chainErase, gateSlots_append, List.length_cons]
    simp only [gateSlots_cons, gateSlots_nil, instructionSlots, List.length_nil, List.length_cons] at h ⊢
    omega

theorem pairEqual_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (t₁ t₂ : Wire)
    (e₁ e₂ : Bool) (C D : Point) : gateSlots (pairEqual L t₁ t₂ e₁ e₂ C D) ≤ 2319 := by
  have hx := Baselines.xorConstant_gateSlots_le (pairSrc L) (pairCode C)
  have hz := zeroWith_pair_slots (yLow L) t₁ t₂ e₁ (yBit C) e₂ (yBit D) L.control (pairPorts L)
  rw [pairSrc_length L hw] at hx
  rw [pairPorts_length L hw] at hz
  simp only [pairEqual, gateSlots_append]
  omega

end ECDSAAdd.Entrant
