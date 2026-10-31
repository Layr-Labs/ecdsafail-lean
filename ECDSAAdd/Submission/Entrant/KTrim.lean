import ECDSAAdd.Arithmetic.InPlaceAdder
import ECDSAAdd.Arithmetic.MappedSubtract
import ECDSAAdd.Arithmetic.MappedDiagonal
import ECDSAAdd.Arithmetic.MappedSources
import ECDSAAdd.Math.SignedSquareIdentity
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Challenge.Contract

/-! KTrim: first majorities of in-place adders whose Toffoli provably never fires.

`majority a b cin c = [CX a b, CX a cin, CCX b cin c, CX a c, CX a cin, CX a b]`. With `cin = 0`
on entry the Toffoli computes `(b ⊕ a) ∧ a = a ∧ ¬b`; whenever that is `false` it is the identity
and is dropped (`majorityT`). The adders below differ from the library ones only in that first
majority, and agree with them on every state satisfying the entry condition. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.KTrim
open ECDSAAdd ECDSAAdd.Arithmetic

def majorityT (a b cin c : Wire) : Program := [.CX a b, .CX a cin, .CX a c, .CX a cin, .CX a b]

theorem run_drop_ccx (P Q : Program) (a b t : Wire) (m : List Bool) (s : State)
    (hP : measurementCount P = 0) (hab : ((run P [] s).basis a && (run P [] s).basis b) = false) :
    run (P ++ (.CCX a b t :: Q)) m s = run (P ++ Q) m s := by
  rw [run_append, run_append P Q, hP]
  simp only [List.take_zero, List.drop_zero, run, hab, Bool.xor_false, writeBit, Function.update_eq_self]

theorem majorityT_run (a b cin c : Wire) (Q : Program) (hab : a ≠ b) (hbc : b ≠ cin)
    (m : List Bool) (s : State) (hcin : s.basis cin = false) (hfire : (s.basis a && !s.basis b) = false) :
    run (majorityT a b cin c ++ Q) m s = run (majority a b cin c ++ Q) m s := by
  have e : majority a b cin c ++ Q =
      [.CX a b, .CX a cin] ++ (.CCX b cin c :: ([.CX a c, .CX a cin, .CX a b] ++ Q)) := rfl
  have e' : majorityT a b cin c ++ Q = [.CX a b, .CX a cin] ++ ([.CX a c, .CX a cin, .CX a b] ++ Q) := rfl
  rw [e, e', run_drop_ccx _ _ _ _ _ _ _ rfl]
  simp only [run, writeBit, Function.update_apply, if_neg hbc, hcin, if_neg (Ne.symm hbc)]
  cases ha : s.basis a <;> cases hb : s.basis b <;> simp_all

theorem majorityT_counts (a b cin c : Wire) :
    toffoliCount (majorityT a b cin c) + 1 = toffoliCount (majority a b cin c) ∧
      measurementCount (majorityT a b cin c) = measurementCount (majority a b cin c) := by
  constructor <;> rfl

/-- `addInPlace` with its first Toffoli dropped. -/
def addInPlaceT : List Wire → List Wire → List Wire → Wire → Program
  | a :: (a' :: as), b :: (b' :: bs), c :: cs, cin =>
      majorityT a b cin c ++ addInPlace (a' :: as) (b' :: bs) cs c ++
        eraseCarry a b cin c ++ [.CX a b, .CX cin b]
  | x, y, carry, cin => addInPlace x y carry cin

/-- Entry condition: `cin = 0` and the first source bit implies the first target bit. -/
def AddOK (x y : List Wire) (cin : Wire) (s : BasisState) : Prop :=
  s cin = false ∧ ∀ a ∈ x.head?, ∀ b ∈ y.head?, (s a && !s b) = false

theorem addInPlaceT_run (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (m : List Bool) (s : State)
    (ok : AddOK x y cin s.basis) :
    run (addInPlaceT x y carry cin) m s = run (addInPlace x y carry cin) m s := by
  match x, y, carry, hnd, ok with
  | a :: (a' :: as), b :: (b' :: bs), c :: cs, hnd, ok =>
    have hab : a ≠ b := by
      intro e; subst e; simp [List.nodup_cons, List.mem_append] at hnd
    have hbc : b ≠ cin := by
      intro e; subst e; simp [List.nodup_cons, List.mem_append] at hnd
    simp only [addInPlaceT, addInPlace, List.append_assoc]
    exact majorityT_run a b cin c _ hab hbc m s ok.1 (ok.2 a rfl b rfl)
  | [], _, _, _, _ => rfl
  | [_], _, _, _, _ => rfl
  | _ :: _ :: _, [], _, _, _ => rfl
  | _ :: _ :: _, [_], _, _, _ => rfl
  | _ :: _ :: _, _ :: _ :: _, [], _, _ => rfl

theorem addInPlaceT_counts (x y carry : List Wire) (cin : Wire) (hx : 2 ≤ x.length) (hy : 2 ≤ y.length)
    (hc : 1 ≤ carry.length) :
    toffoliCount (addInPlaceT x y carry cin) + 1 = toffoliCount (addInPlace x y carry cin) ∧
      measurementCount (addInPlaceT x y carry cin) = measurementCount (addInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a :: (a' :: as), b :: (b' :: bs), c :: cs, _, _, _ =>
    simp only [addInPlaceT, addInPlace, toffoliCount_append, measurementCount_append]
    have := majorityT_counts a b cin c
    omega

theorem addInPlaceT_meas (x y carry : List Wire) (cin : Wire) :
    measurementCount (addInPlaceT x y carry cin) = measurementCount (addInPlace x y carry cin) := by
  match x, y, carry with
  | a :: (a' :: as), b :: (b' :: bs), c :: cs =>
    simp only [addInPlaceT, addInPlace, measurementCount_append]
    rw [(majorityT_counts a b cin c).2]
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | _ :: _ :: _, [], _ => rfl
  | _ :: _ :: _, [_], _ => rfl
  | _ :: _ :: _, _ :: _ :: _, [] => rfl

/-- `subInPlace` with its first Toffoli dropped. -/
def subInPlaceT (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addInPlaceT x y carry cin ++ notRegister y

/-- Entry condition for a subtraction: `cin = 0` and the first bits are not both set. -/
def SubOK (x y : List Wire) (cin : Wire) (s : BasisState) : Prop :=
  s cin = false ∧ ∀ a ∈ x.head?, ∀ b ∈ y.head?, (s a && s b) = false

theorem subInPlaceT_run (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (m : List Bool) (s : State)
    (ok : SubOK x y cin s.basis) :
    run (subInPlaceT x y carry cin) m s = run (subInPlace x y carry cin) m s := by
  have hy : y.Nodup := by
    have := (List.nodup_cons.mp hnd).2
    exact (List.nodup_append.mp (List.nodup_append.mp this).1).2.1
  have hcy : cin ∉ y := by
    intro h; exact (List.nodup_cons.mp hnd).1 (by simp [h])
  have hxy : ∀ a ∈ x, a ∉ y := by
    intro a ha hb
    have := (List.nodup_cons.mp hnd).2
    exact (List.nodup_append.mp (List.nodup_append.mp this).1).2.2 a ha a hb rfl
  rw [subInPlaceT, subInPlace, run_append, run_append (notRegister y ++ addInPlace x y carry cin),
    run_append, run_append (notRegister y)]
  have mc : measurementCount (notRegister y) = 0 := (notRegister_counts y).2
  rw [mc]
  simp only [List.take_zero, List.drop_zero]
  rw [addInPlaceT_run x y carry cin hnd, measurementCount_append, measurementCount_append,
    addInPlaceT_meas]
  · rw [notRegister_correct y hy]
    refine ⟨by simp [hcy, ok.1], ?_⟩
    intro a ha b hb
    have ha' : a ∉ y := hxy a (List.mem_of_mem_head? ha)
    have hb' : b ∈ y := List.mem_of_mem_head? hb
    simp only [ha', hb', if_false, if_true, Bool.not_not]
    exact ok.2 a ha b hb

theorem subInPlaceT_counts (x y carry : List Wire) (cin : Wire) (hx : 2 ≤ x.length) (hy : 2 ≤ y.length)
    (hc : 1 ≤ carry.length) :
    toffoliCount (subInPlaceT x y carry cin) + 1 = toffoliCount (subInPlace x y carry cin) ∧
      measurementCount (subInPlaceT x y carry cin) = measurementCount (subInPlace x y carry cin) := by
  have h := addInPlaceT_counts x y carry cin hx hy hc
  simp only [subInPlaceT, subInPlace, toffoliCount_append, measurementCount_append]
  omega

/-- First mapped majority without its Toffoli, for a plain wire source bit. -/
def mappedMajorityT (b : MappedBit) (y cin c : Wire) : Program :=
  match b with
  | ⟨some a, false⟩ => majorityT a y cin c
  | _ => mappedMajority b y cin c

/-- `mappedAdd` with its first Toffoli dropped (when the first bit is a plain wire). -/
def mappedAddT : List MappedBit → List Wire → List Wire → Wire → Program
  | b :: b' :: bits, y :: y' :: ys, c :: cs, cin =>
      mappedMajorityT b y cin c ++ mappedAdd (b' :: bits) (y' :: ys) cs c ++
        mappedEraseCarry b y cin c ++ mappedSum b y cin
  | bits, ys, carry, cin => mappedAdd bits ys carry cin

def MappedOK (bits : List MappedBit) (ys : List Wire) (cin : Wire) (s : BasisState) : Prop :=
  s cin = false ∧ ∀ b ∈ bits.head?, ∀ y ∈ ys.head?, (b.value s && !s y) = false

theorem mappedAddT_run (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hnd : (cin :: (ys ++ carry)).Nodup) (hsrc : ∀ q ∈ mappedWires bits, q ∉ cin :: (ys ++ carry))
    (m : List Bool) (s : State) (ok : MappedOK bits ys cin s.basis) :
    run (mappedAddT bits ys carry cin) m s = run (mappedAdd bits ys carry cin) m s := by
  match bits, ys, carry, hnd, hsrc, ok with
  | b :: b' :: bits, y :: y' :: ys, c :: cs, hnd, hsrc, ok =>
    simp only [mappedAddT, mappedAdd, List.append_assoc]
    match b, hsrc, ok with
    | ⟨some a, false⟩, hsrc, ok =>
      have hay : a ≠ y := by
        intro e; subst e
        exact hsrc a (by simp [mappedWires]) (by simp)
      have hyc : y ≠ cin := by
        intro e; subst e; simp [List.nodup_cons] at hnd
      have f := ok.2 ⟨some a, false⟩ rfl y rfl
      simp only [MappedBit.value, Option.map_some, Option.getD_some, Bool.false_xor] at f
      exact majorityT_run a y cin c _ hay hyc m s ok.1 f
    | ⟨some a, true⟩, _, _ => rfl
    | ⟨none, fl⟩, _, _ => rfl
  | [], _, _, _, _, _ => rfl
  | [_], _, _, _, _, _ => rfl
  | _ :: _ :: _, [], _, _, _, _ => rfl
  | _ :: _ :: _, [_], _, _, _, _ => rfl
  | _ :: _ :: _, _ :: _ :: _, [], _, _, _ => rfl

theorem mappedMajorityT_counts (b : MappedBit) (y cin c : Wire) (hb : b.wire.isSome ∧ b.flip = false) :
    toffoliCount (mappedMajorityT b y cin c) + 1 = toffoliCount (mappedMajority b y cin c) ∧
      measurementCount (mappedMajorityT b y cin c) = measurementCount (mappedMajority b y cin c) := by
  match b, hb with
  | ⟨some a, false⟩, _ => constructor <;> rfl

theorem mappedMajorityT_meas (b : MappedBit) (y cin c : Wire) :
    measurementCount (mappedMajorityT b y cin c) = measurementCount (mappedMajority b y cin c) := by
  match b with
  | ⟨some a, false⟩ => rfl
  | ⟨some a, true⟩ => rfl
  | ⟨none, fl⟩ => rfl

theorem mappedAddT_meas (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    measurementCount (mappedAddT bits ys carry cin) = measurementCount (mappedAdd bits ys carry cin) := by
  match bits, ys, carry with
  | b :: b' :: bits, y :: y' :: ys, c :: cs =>
    simp only [mappedAddT, mappedAdd, measurementCount_append, mappedMajorityT_meas]
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | _ :: _ :: _, [], _ => rfl
  | _ :: _ :: _, [_], _ => rfl
  | _ :: _ :: _, _ :: _ :: _, [] => rfl

theorem mappedAddT_counts (b b' : MappedBit) (bits : List MappedBit) (y y' : Wire) (ys : List Wire)
    (c : Wire) (cs : List Wire) (cin : Wire) (hb : b.wire.isSome ∧ b.flip = false) :
    toffoliCount (mappedAddT (b :: b' :: bits) (y :: y' :: ys) (c :: cs) cin) + 1 =
      toffoliCount (mappedAdd (b :: b' :: bits) (y :: y' :: ys) (c :: cs) cin) := by
  simp only [mappedAddT, mappedAdd, toffoliCount_append]
  have := (mappedMajorityT_counts b y cin c hb).1
  omega

def mappedDiagSubT (xs dst carry : List Wire) (cin : Wire) : Program :=
  notRegister dst ++ mappedAddT (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin ++ notRegister dst

def mappedDiagAddT (xs dst carry : List Wire) (cin : Wire) : Program :=
  mappedAddT (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin

/-- `x^2 + signedDiagValue x n` is even for `n ≥ 1` (both `x^2+x` and the `2^n` multiple are). -/
theorem sq_diag_even (x n : Nat) (hn : 1 ≤ n) : (x^2+signedDiagValue x n) % 2 = 0 := by
  unfold signedDiagValue
  rw [if_neg (by omega)]
  have h2 : 2 ∣ 2^n := dvd_pow_self 2 (by omega)
  obtain ⟨k, hk⟩ := h2
  rw [hk]
  have : (x^2 + (x + (2^(n-1)-1-x%2^(n-1))*(2*k))) % 2 = (x^2 + x) % 2 := by
    rw [show x^2 + (x + (2^(n-1)-1-x%2^(n-1))*(2*k)) = (x^2 + x) + 2*((2^(n-1)-1-x%2^(n-1))*k) by ring]
    omega
  rw [this]
  rcases Nat.even_or_odd x with ⟨r, hr⟩ | ⟨r, hr⟩ <;> subst hr <;> ring_nf <;> omega

/-- The low wire of a register whose value is congruent to an even number is clear. -/
theorem head_false_of_even (w : Wire) (ws : List Wire) (s : BasisState) (x : Int)
    (hx : (regValue (w :: ws) s : Int) ≡ x [ZMOD (2^(w :: ws).length : Nat)]) (he : x % 2 = 0) :
    s w = false := by
  have h2 : ((2 : Nat) : Int) ∣ ((2^(w :: ws).length : Nat) : Int) := by
    have : (2 : Nat) ∣ 2^(w :: ws).length := dvd_pow_self 2 (by simp)
    exact_mod_cast this
  have hm := Int.ModEq.of_dvd h2 hx
  have e : regValue (w :: ws) s = (if s w then 1 else 0) + 2 * regValue ws s := rfl
  rw [e] at hm
  unfold Int.ModEq at hm
  cases hw : s w <;> simp_all <;> omega

theorem head_bit_mod2 (w : Wire) (ws : List Wire) (s : BasisState) (x : Int)
    (hx : (regValue (w :: ws) s : Int) ≡ x [ZMOD (2^(w :: ws).length : Nat)]) :
    s w = decide (x % 2 = 1) := by
  have h2 : ((2 : Nat) : Int) ∣ ((2^(w :: ws).length : Nat) : Int) := by
    have : (2 : Nat) ∣ 2^(w :: ws).length := dvd_pow_self 2 (by simp)
    exact_mod_cast this
  have hm := Int.ModEq.of_dvd h2 hx
  have e : regValue (w :: ws) s = (if s w then 1 else 0) + 2 * regValue ws s := rfl
  rw [e] at hm
  unfold Int.ModEq at hm
  cases hw : s w <;> simp_all <;> omega

/-- A register congruent to `x^2` has the low bit of a register holding `x`. -/
theorem head_eq_of_sq (d l : Wire) (ds ls : List Wire) (s : BasisState) (x : Nat)
    (hd : (regValue (d :: ds) s : Int) ≡ ((x^2 : Nat) : Int) [ZMOD (2^(d :: ds).length : Nat)])
    (hl : regValue (l :: ls) s = x) : s d = s l := by
  rw [head_bit_mod2 d ds s _ hd]
  have hl' : ((regValue (l :: ls) s : Nat) : Int) ≡ ((x : Nat) : Int) [ZMOD (2^(l :: ls).length : Nat)] := by
    rw [hl]
  rw [head_bit_mod2 l ls s _ hl']
  have h : x^2 % 2 = x % 2 := by
    rcases Nat.mod_two_eq_zero_or_one x with h|h <;> simp [Nat.pow_mod, h]
  have h' : ((x^2 % 2 : Nat) : Int) = ((x % 2 : Nat) : Int) := by rw [h]
  simp only [Int.natCast_mod, Nat.cast_ofNat] at h'
  rw [h']

def mappedSubT (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) : Program :=
  notRegister ys ++ mappedAddT bits ys carry cin ++ notRegister ys

theorem mappedSubT_run (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hnd : (cin :: (ys ++ carry)).Nodup) (hsrc : ∀ q ∈ mappedWires bits, q ∉ cin :: (ys ++ carry))
    (m : List Bool) (s : State) (hcin : s.basis cin = false)
    (ok : ∀ b ∈ bits.head?, ∀ y ∈ ys.head?, (b.value s.basis && s.basis y) = false) :
    run (mappedSubT bits ys carry cin) m s = run (mappedSub bits ys carry cin) m s := by
  have hy : ys.Nodup := (List.nodup_append.mp (List.nodup_cons.mp hnd).2).1
  have hcy : cin ∉ ys := by intro h; exact (List.nodup_cons.mp hnd).1 (by simp [h])
  rw [mappedSubT, mappedSub, run_append, run_append (notRegister ys ++ mappedAdd bits ys carry cin),
    run_append, run_append (notRegister ys)]
  have mc : measurementCount (notRegister ys) = 0 := (notRegister_counts ys).2
  rw [mc]
  simp only [List.take_zero, List.drop_zero]
  rw [mappedAddT_run bits ys carry cin hnd hsrc, measurementCount_append, measurementCount_append,
    mappedAddT_meas]
  rw [notRegister_correct ys hy]
  refine ⟨by simp [hcy, hcin], ?_⟩
  intro b hb y hy'
  have hy'' : y ∈ ys := List.mem_of_mem_head? hy'
  have hsrcb : ∀ q ∈ b.wire, q ∉ ys := by
    intro q hq hm
    have hbm : b ∈ bits := List.mem_of_mem_head? hb
    have : q ∈ mappedWires bits := List.mem_flatMap.mpr ⟨b, hbm, by simp [Option.mem_def.mp hq]⟩
    exact hsrc q this (by simp [hm])
  have hv : b.value (fun w => if w ∈ ys then !s.basis w else s.basis w) = b.value s.basis := by
    unfold MappedBit.value
    cases hw : b.wire with
    | none => rfl
    | some q => simp [hsrcb q hw]
  simp only [hv, hy'', if_true, Bool.not_not]
  exact ok b hb y hy'

/-! ### Support, physicality and slots: each trimmed program deletes one instruction. -/

theorem del_wires (P Q : Program) (i : Instr) : wires (P ++ Q) ⊆ wires (P ++ i :: Q) := by
  rw [wires_append, show P ++ i :: Q = P ++ [i] ++ Q by simp, wires_append, wires_append]
  exact Finset.union_subset_union (Finset.subset_union_left) (Finset.Subset.refl _)

theorem del_physical (P Q : Program) (i : Instr) (h : GatePhysical (P ++ i :: Q)) : GatePhysical (P ++ Q) := by
  rw [show P ++ i :: Q = P ++ [i] ++ Q by simp] at h
  simp only [gatePhysical_append] at h ⊢
  exact ⟨h.1.1, h.2⟩

theorem del_slots (P Q : Program) (i : Instr) :
    Challenge.gateSlots (P ++ Q) + 1 ≤ Challenge.gateSlots (P ++ i :: Q) := by
  rw [show P ++ i :: Q = P ++ [i] ++ Q by simp]
  simp only [Challenge.gateSlots_append]
  have : 1 ≤ Challenge.gateSlots [i] := by
    cases i <;> simp [Challenge.gateSlots, Challenge.instructionSlots] <;> omega
  omega

theorem majority_del (a b cin c : Wire) (Q : Program) :
    majority a b cin c ++ Q = [.CX a b, .CX a cin] ++ (.CCX b cin c :: ([.CX a c, .CX a cin, .CX a b] ++ Q)) ∧
    majorityT a b cin c ++ Q = [.CX a b, .CX a cin] ++ ([.CX a c, .CX a cin, .CX a b] ++ Q) := ⟨rfl, rfl⟩

/-- Generic transfer for any one-instruction deletion `T` of `P`. -/
structure Del (T P : Program) : Prop where
  wires : wires T ⊆ wires P
  physical : GatePhysical P → GatePhysical T
  slots : Challenge.gateSlots T ≤ Challenge.gateSlots P

theorem Del.ofSplit {T P : Program} (A B : Program) (i : Instr) (hT : T = A ++ B) (hP : P = A ++ i :: B) :
    Del T P := by
  subst hT; subst hP
  exact ⟨del_wires A B i, del_physical A B i, by have := del_slots A B i; omega⟩

theorem Del.refl (P : Program) : Del P P := ⟨Finset.Subset.refl _, id, le_refl _⟩

theorem Del.append_right {T P : Program} (h : Del T P) (Q : Program) : Del (T ++ Q) (P ++ Q) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [wires_append]; exact Finset.union_subset_union h.wires (Finset.Subset.refl _)
  · simp only [gatePhysical_append]; exact fun h' => ⟨h.physical h'.1, h'.2⟩
  · simp only [Challenge.gateSlots_append]; have := h.slots; omega

theorem Del.append_left {T P : Program} (h : Del T P) (Q : Program) : Del (Q ++ T) (Q ++ P) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [wires_append]; exact Finset.union_subset_union (Finset.Subset.refl _) h.wires
  · simp only [gatePhysical_append]; exact fun h' => ⟨h'.1, h.physical h'.2⟩
  · simp only [Challenge.gateSlots_append]; have := h.slots; omega

theorem addInPlaceT_del (x y carry : List Wire) (cin : Wire) :
    Del (addInPlaceT x y carry cin) (addInPlace x y carry cin) := by
  match x, y, carry with
  | a :: (a' :: as), b :: (b' :: bs), c :: cs =>
    simp only [addInPlaceT, addInPlace, List.append_assoc]
    exact Del.ofSplit _ _ _ (majority_del a b cin c _).2 (majority_del a b cin c _).1
  | [], _, _ => exact Del.refl _
  | [_], _, _ => exact Del.refl _
  | _ :: _ :: _, [], _ => exact Del.refl _
  | _ :: _ :: _, [_], _ => exact Del.refl _
  | _ :: _ :: _, _ :: _ :: _, [] => exact Del.refl _

theorem subInPlaceT_del (x y carry : List Wire) (cin : Wire) :
    Del (subInPlaceT x y carry cin) (subInPlace x y carry cin) :=
  ((addInPlaceT_del x y carry cin).append_left (notRegister y)).append_right (notRegister y)

theorem mappedMajorityT_del (b : MappedBit) (y cin c : Wire) (Q : Program) :
    Del (mappedMajorityT b y cin c ++ Q) (mappedMajority b y cin c ++ Q) := by
  match b with
  | ⟨some a, false⟩ => exact Del.ofSplit _ _ _ (majority_del a y cin c Q).2 (majority_del a y cin c Q).1
  | ⟨some a, true⟩ => exact Del.refl _
  | ⟨none, fl⟩ => exact Del.refl _

theorem mappedAddT_del (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    Del (mappedAddT bits ys carry cin) (mappedAdd bits ys carry cin) := by
  match bits, ys, carry with
  | b :: b' :: bits, y :: y' :: ys, c :: cs =>
    simp only [mappedAddT, mappedAdd, List.append_assoc]
    exact mappedMajorityT_del b y cin c _
  | [], _, _ => exact Del.refl _
  | [_], _, _ => exact Del.refl _
  | _ :: _ :: _, [], _ => exact Del.refl _
  | _ :: _ :: _, [_], _ => exact Del.refl _
  | _ :: _ :: _, _ :: _ :: _, [] => exact Del.refl _

theorem mappedSubT_del (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    Del (mappedSubT bits ys carry cin) (mappedSub bits ys carry cin) :=
  ((mappedAddT_del bits ys carry cin).append_left (notRegister ys)).append_right (notRegister ys)

/-! ### Wrappers in the `(cin::xs++dst++carry).Nodup` form used by the square proofs. -/

theorem nd_form {cin : Wire} {x y c : List Wire} (h : (cin::x++y++c).Nodup) : (cin :: (x ++ y ++ c)).Nodup := by
  simpa [List.append_assoc] using h

theorem subT_run (xs dst carry : List Wire) (cin : Wire) (hn : (cin::xs++dst++carry).Nodup)
    (m : List Bool) (s : State) (hi : s.basis cin = false) (h0 : ∀ a ∈ xs.head?, s.basis a = false) :
    run (subInPlaceT xs dst carry cin) m s = run (subInPlace xs dst carry cin) m s :=
  subInPlaceT_run xs dst carry cin (nd_form hn) m s ⟨hi, fun a ha b _ => by simp [h0 a ha]⟩

theorem addT_run (xs dst carry : List Wire) (cin : Wire) (hn : (cin::xs++dst++carry).Nodup)
    (m : List Bool) (s : State) (hi : s.basis cin = false) (h0 : ∀ a ∈ xs.head?, s.basis a = false) :
    run (addInPlaceT xs dst carry cin) m s = run (addInPlace xs dst carry cin) m s :=
  addInPlaceT_run xs dst carry cin (nd_form hn) m s ⟨hi, fun a ha b _ => by simp [h0 a ha]⟩

theorem diag_src (xs dst carry : List Wire) (cin : Wire) (hn : (cin::xs++dst++carry).Nodup) :
    ∀ q ∈ mappedWires (mappedDiagonal xs), q ∉ cin :: (dst ++ carry.take (dst.length-1)) := by
  intro q hq hm
  rw [mappedDiagonal_wires] at hq
  have hqx : q ∈ xs := by
    rcases List.mem_append.mp hq with h|h
    · exact h
    · exact List.mem_of_mem_take h
  have hn' := nd_form hn
  simp only [List.mem_cons, List.mem_append] at hm
  rcases hm with e|e|e
  · subst e; exact (List.nodup_cons.mp hn').1 (by simp [hqx])
  · have := (List.nodup_cons.mp hn').2
    exact (List.nodup_append.mp (List.nodup_append.mp this).1).2.2 q hqx q e rfl
  · have := (List.nodup_cons.mp hn').2
    exact (List.nodup_append.mp this).2.2 q (List.mem_append_left _ hqx) q (List.mem_of_mem_take e) rfl

theorem diag_nd (xs dst carry : List Wire) (cin : Wire) (hn : (cin::xs++dst++carry).Nodup) :
    (cin :: (dst ++ carry.take (dst.length-1))).Nodup := by
  have hn' := nd_form hn
  have sub : List.Sublist (cin :: (dst ++ carry.take (dst.length-1))) (cin :: (xs ++ dst ++ carry)) := by
    apply List.Sublist.cons₂
    rw [List.append_assoc]
    exact List.Sublist.trans (List.Sublist.append (List.Sublist.refl dst) (List.take_sublist _ _))
      (List.sublist_append_right xs _)
  exact sub.nodup hn'

theorem diag_head (xs : List Wire) (x : Wire) (hx : x ∈ xs.head?) :
    (⟨some x, false⟩ : MappedBit) ∈ (mappedDiagonal xs).head? := by
  match xs, hx with
  | x0 :: _, hx =>
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
    subst hx
    simp [mappedDiagonal, mappedRead]

theorem diag_head_only (xs : List Wire) (b : MappedBit) (hb : b ∈ (mappedDiagonal xs).head?) :
    (∃ x ∈ xs.head?, b = ⟨some x, false⟩) ∨ b = ⟨none, false⟩ := by
  match xs, hb with
  | x0 :: _, hb =>
    simp [mappedDiagonal, mappedRead] at hb
    exact Or.inl ⟨x0, rfl, hb.symm⟩
  | [], hb =>
    simp [mappedDiagonal, mappedRead] at hb
    exact Or.inr hb.symm

theorem dsubT_run (xs dst carry : List Wire) (cin : Wire) (hn : (cin::xs++dst++carry).Nodup)
    (m : List Bool) (s : State) (hi : s.basis cin = false) (h0 : ∀ y ∈ dst.head?, s.basis y = false) :
    run (mappedDiagSubT xs dst carry cin) m s = run (mappedDiagSub xs dst carry cin) m s :=
  mappedSubT_run _ _ _ _ (diag_nd xs dst carry cin hn) (diag_src xs dst carry cin hn) m s hi
    (fun b _ y hy => by simp [h0 y hy])

theorem daddT_run (xs dst carry : List Wire) (cin : Wire) (hn : (cin::xs++dst++carry).Nodup)
    (m : List Bool) (s : State) (hi : s.basis cin = false)
    (h0 : ∀ x ∈ xs.head?, ∀ y ∈ dst.head?, s.basis y = s.basis x) :
    run (mappedDiagAddT xs dst carry cin) m s = run (mappedDiagAdd xs dst carry cin) m s := by
  apply mappedAddT_run _ _ _ _ (diag_nd xs dst carry cin hn) (diag_src xs dst carry cin hn) m s
  refine ⟨hi, fun b hb y hy => ?_⟩
  rcases diag_head_only xs b hb with ⟨x, hx, rfl⟩ | rfl
  · simp [MappedBit.value, h0 x hx y hy]
  · simp [MappedBit.value]

theorem dsubT_del (xs dst carry : List Wire) (cin : Wire) :
    Del (mappedDiagSubT xs dst carry cin) (mappedDiagSub xs dst carry cin) :=
  mappedSubT_del _ _ _ _

theorem daddT_del (xs dst carry : List Wire) (cin : Wire) :
    Del (mappedDiagAddT xs dst carry cin) (mappedDiagAdd xs dst carry cin) :=
  mappedAddT_del _ _ _ _

theorem daddT_counts (xs dst carry : List Wire) (cin : Wire) (hx : 1 ≤ xs.length) (hd : 2 ≤ dst.length)
    (hc : dst.length - 1 ≤ carry.length) :
    toffoliCount (mappedDiagAddT xs dst carry cin) + 1 = toffoliCount (mappedDiagAdd xs dst carry cin) ∧
      measurementCount (mappedDiagAddT xs dst carry cin) = measurementCount (mappedDiagAdd xs dst carry cin) := by
  refine ⟨?_, mappedAddT_meas _ _ _ _⟩
  unfold mappedDiagAddT mappedDiagAdd
  match xs, dst, hx, hd with
  | x0 :: xs', y0 :: y1 :: ys, _, _ =>
    have hcl : 1 ≤ (carry.take ((y0 :: y1 :: ys).length - 1)).length := by
      simp only [List.length_take, List.length_cons]; omega
    match hct : carry.take ((y0 :: y1 :: ys).length - 1), hcl with
    | c0 :: cs, _ =>
      have hm : ∃ b' bits, mappedDiagonal (x0 :: xs') = ⟨some x0, false⟩ :: b' :: bits := by
        cases xs' with
        | nil => exact ⟨_, _, rfl⟩
        | cons x1 xs'' => exact ⟨_, _, rfl⟩
      obtain ⟨b', bits, hb⟩ := hm
      rw [hb]
      exact mappedAddT_counts _ b' bits y0 y1 ys c0 cs cin ⟨rfl, rfl⟩

theorem dsubT_counts (xs dst carry : List Wire) (cin : Wire) (hx : 1 ≤ xs.length) (hd : 2 ≤ dst.length)
    (hc : dst.length - 1 ≤ carry.length) :
    toffoliCount (mappedDiagSubT xs dst carry cin) + 1 = toffoliCount (mappedDiagSub xs dst carry cin) ∧
      measurementCount (mappedDiagSubT xs dst carry cin) = measurementCount (mappedDiagSub xs dst carry cin) := by
  have h := daddT_counts xs dst carry cin hx hd hc
  unfold mappedDiagAddT mappedDiagAdd at h
  simp only [mappedDiagSubT, mappedDiagSub, mappedSub, toffoliCount_append, measurementCount_append]
  omega

theorem Del.app {T P T' P' : Program} (h : Del T P) (h' : Del T' P') : Del (T ++ T') (P ++ P') := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [wires_append]; exact Finset.union_subset_union h.wires h'.wires
  · simp only [gatePhysical_append]; exact fun g => ⟨h.physical g.1, h'.physical g.2⟩
  · simp only [Challenge.gateSlots_append]; have := h.slots; have := h'.slots; omega

theorem subInPlaceT_meas (x y carry : List Wire) (cin : Wire) :
    measurementCount (subInPlaceT x y carry cin) = measurementCount (subInPlace x y carry cin) := by
  simp only [subInPlaceT, subInPlace, measurementCount_append, addInPlaceT_meas]

end ECDSAAdd.Entrant.KTrim
