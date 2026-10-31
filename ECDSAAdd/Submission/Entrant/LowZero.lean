import ECDSAAdd.Arithmetic.InPlaceAdder
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.Registers
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Arithmetic.BalancedFieldInverseArithmetic

/-! LowZero: an in-place addition whose lowest source bit and carry-in are both zero.

Bit 0 of the target is then unchanged and no carry leaves bit 0, so the lowest
majority / measured-erase pair of `addInPlace` (one Toffoli, one measurement) and the
final two CNOTs of that bit are dropped; the remaining bits are added with the original
carry-in wire, which is still zero. -/

set_option maxHeartbeats 1000000

namespace ECDSAAdd.Entrant.LowZero
open ECDSAAdd ECDSAAdd.Arithmetic

/-- `addInPlace` restricted to bits `1..n-1`; the dropped (clean) lowest carry wire is
measured with empty corrections so the measurement count and record layout are kept. -/
def addLow0 (x y carry : List Wire) (cin : Wire) : Program :=
  addInPlace x.tail y.tail carry.tail cin ++ [.measureX (carry.headD 0) [] []]

theorem foldr_cons_value (w : Wire) (r : List Wire) (st : BasisState) :
    regValue (w :: r) st = (if st w then 1 else 0) + 2 * regValue r st := rfl

theorem measure_zero_id (c : Wire) (m : List Bool) (t : State) (h : t.basis c = false) :
    run [.measureX c [] []] m t = t := by
  obtain ⟨ph, bs⟩ := t
  simp only at h
  have e : writeBit bs c false = bs := by
    funext q; by_cases hq : q = c
    · subst hq; simp [writeBit, h]
    · simp [writeBit, Function.update, hq]
  simp only [run, measureAndCorrect, h, Bool.and_false, Bool.xor_false, e]
  cases m.headD false <;> rfl

theorem low_mod (d A k : Nat) (hd : d < 2) :
    d + 2 * (A % 2^k) = (d + 2 * A) % (2^k * 2) := by
  have hr := Nat.mod_lt A (Nat.two_pow_pos k)
  have e := Nat.div_add_mod A (2^k)
  have key : d + 2 * A = (d + 2 * (A % 2^k)) + (2^k * 2) * (A / 2^k) := by
    conv_lhs => rw [← e]
    ring
  rw [key, Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem addLow0_correct (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) (s : State) (m : List Bool)
    (hclean : ∀ w ∈ carry, s.basis w = false)
    (hx0 : s.basis (x.headD 0) = false) (hcin : s.basis cin = false) :
    (run (addLow0 x y carry cin) m s).phase = s.phase ∧
    (∀ w, w ∉ y → (run (addLow0 x y carry cin) m s).basis w = s.basis w) ∧
    regValue y (run (addLow0 x y carry cin) m s).basis =
      (regValue x s.basis + regValue y s.basis + (s.basis cin).toNat) % 2^y.length := by
  rcases x with _ | ⟨a, as⟩
  · simp at hx h2; omega
  rcases y with _ | ⟨b, bs⟩
  · simp at hx h2
  rcases carry with _ | ⟨c, cs⟩
  · simp only [List.length_cons, List.length_nil] at hc h2; omega
  · simp only [List.headD_cons] at hx0
    simp only [List.length_cons] at hx hc h2
    have hnd' : (cin :: (as ++ bs ++ cs)).Nodup := by
      apply List.Nodup.sublist _ hnd
      apply List.Sublist.cons₂
      simp only [List.cons_append, List.append_assoc]
      apply List.Sublist.cons
      apply List.Sublist.append_left
      apply List.Sublist.cons
      apply List.Sublist.append_left
      exact List.sublist_cons_self c cs
    have hb : b ∉ bs := by
      have h := List.nodup_cons.mp hnd
      have h' := (List.nodup_append.mp (List.nodup_append.mp h.2).1).2.1
      exact (List.nodup_cons.mp h').1
    have hcy : c ∉ bs := by
      intro hc'
      have h := (List.nodup_cons.mp hnd).2
      rw [List.nodup_append] at h
      exact h.2.2 c (List.mem_append_right _ (List.mem_cons_of_mem b hc')) c List.mem_cons_self rfl
    let k := measurementCount (addInPlace as bs cs cin)
    have r := addInPlace_correct as bs cs cin hnd' (by omega) (by omega) s (m.take k)
      (fun w hw => hclean w (List.mem_cons_of_mem c hw))
    have e : run (addLow0 (a :: as) (b :: bs) (c :: cs) cin) m s =
        run (addInPlace as bs cs cin) (m.take k) s := by
      simp only [addLow0, List.tail_cons, List.headD_cons]
      rw [run_append, measure_zero_id]
      rw [r.2.1 c hcy]
      exact hclean c List.mem_cons_self
    rw [e]
    refine ⟨r.1, fun w hw => r.2.1 w (fun h => hw (List.mem_cons_of_mem b h)), ?_⟩
    rw [foldr_cons_value, foldr_cons_value, foldr_cons_value, r.2.1 b hb, r.2.2, hx0, hcin]
    simp only [Bool.false_eq_true, if_false, Bool.toNat_false, Nat.add_zero, Nat.zero_add,
      List.length_cons, pow_succ]
    rw [show 2 * regValue as s.basis + ((if s.basis b = true then 1 else 0) + 2 * regValue bs s.basis) =
        (if s.basis b = true then 1 else 0) + 2 * (regValue as s.basis + regValue bs s.basis) by ring]
    exact low_mod _ _ _ (by split <;> omega)

theorem addLow0_counts (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    toffoliCount (addLow0 x y carry cin) = y.length - 2 ∧
    measurementCount (addLow0 x y carry cin) = y.length - 1 := by
  have h := addInPlace_counts x.tail y.tail carry.tail cin
    (by simp only [List.length_tail]; omega) (by simp only [List.length_tail]; omega)
  simp only [List.length_tail] at h
  simp only [addLow0, toffoliCount_append, measurementCount_append, h.1, h.2]
  simp [toffoliCount, measurementCount]; omega

theorem addLow0_wires (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    wires (addLow0 x y carry cin) ⊆ (cin :: (x ++ y ++ carry)).toFinset := by
  unfold addLow0
  rw [wires_append, addInPlace_wires x.tail y.tail carry.tail cin
    (by simp only [List.length_tail]; omega) (by simp only [List.length_tail]; omega)]
  apply Finset.union_subset
  · intro q hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hq ⊢
    rcases hq with h | (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl (List.mem_of_mem_tail h)))
    · exact Or.inr (Or.inl (Or.inr (List.mem_of_mem_tail h)))
    · exact Or.inr (Or.inr (List.mem_of_mem_tail h))
  · intro q hq
    rcases carry with _ | ⟨c, cs⟩
    · simp only [List.length_nil] at hc; omega
    · simp [wires, Instr.wires, correctionWires] at hq
      subst hq
      simp

theorem addLow0_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) : GatePhysical (addLow0 x y carry cin) := by
  unfold addLow0
  rw [gatePhysical_append]
  refine ⟨?_, ?_⟩
  · apply addInPlace_physical
    apply List.Nodup.sublist _ hn
    simp only [List.cons_append, List.append_assoc]
    apply List.Sublist.cons₂
    exact (List.tail_sublist x).append ((List.tail_sublist y).append (List.tail_sublist carry))
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    trivial

theorem addInPlace_slots_cin (x y cs : List Wire) (c c' : Wire) :
    Challenge.gateSlots (addInPlace x y cs c) = Challenge.gateSlots (addInPlace x y cs c') := by
  match x, y, cs with
  | a :: a' :: as, b :: b' :: bs, d :: ds =>
    simp [addInPlace, Challenge.gateSlots, Challenge.instructionSlots, majority, eraseCarry]
  | [a], [b], _ => simp [addInPlace, Challenge.gateSlots, Challenge.instructionSlots]
  | [], _, _ => simp [addInPlace]
  | [_], [], _ => simp [addInPlace]
  | [_], _ :: _ :: _, _ => simp [addInPlace]
  | _ :: _ :: _, [], _ => simp [addInPlace]
  | _ :: _ :: _, [_], _ => simp [addInPlace]
  | _ :: _ :: _, _ :: _ :: _, [] => simp [addInPlace]

theorem addLow0_slots (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    Challenge.gateSlots (addLow0 x y carry cin) ≤ Challenge.gateSlots (addInPlace x y carry cin) := by
  unfold addLow0
  rw [Challenge.gateSlots_append]
  have m1 : Challenge.gateSlots [Instr.measureX (carry.headD 0) [] []] = 1 := by
    simp [Challenge.gateSlots, Challenge.instructionSlots]
  rw [m1]
  rcases x with _ | ⟨a, _ | ⟨a', as⟩⟩
  · simp at hx; omega
  · simp at hx; omega
  rcases y with _ | ⟨b, _ | ⟨b', bs⟩⟩
  · simp at h2
  · simp at h2
  rcases carry with _ | ⟨c, cs⟩
  · simp at hc
  simp only [List.tail_cons, addInPlace, Challenge.gateSlots_append]
  rw [addInPlace_slots_cin (a' :: as) (b' :: bs) cs cin c]
  simp [Challenge.gateSlots, Challenge.instructionSlots, majority, eraseCarry]
  omega

/-- The lowest wire of a register holding an even value is zero. -/
theorem head_false_of_even (r tail : List Wire) (st : BasisState) (k : Nat)
    (h : regValue r st = 2 * k) (hne : r ≠ []) : st ((r ++ tail).headD 0) = false := by
  match r, hne with
  | w :: ws, _ =>
    simp only [List.cons_append, List.headD_cons]
    rw [foldr_cons_value] at h
    by_cases hw : st w = true
    · rw [hw] at h; simp only [if_true] at h; omega
    · simpa using hw

theorem addLow0_wires_sub (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    wires (addLow0 x y carry cin) ⊆ wires (addInPlace x y carry cin) := by
  rw [addInPlace_wires x y carry cin hx hc]
  exact addLow0_wires x y carry cin hx hc h2

theorem addLow0_counts_rel (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    toffoliCount (addLow0 x y carry cin) + 1 = toffoliCount (addInPlace x y carry cin) ∧
    measurementCount (addLow0 x y carry cin) = measurementCount (addInPlace x y carry cin) := by
  have a := addLow0_counts x y carry cin hx hc h2
  have b := addInPlace_counts x y carry cin hx hc
  omega


/-! ### Bit 0 that emits no carry

If `cin = 0` and the two lowest operand bits are not both one, bit 0 produces no carry: only
its sum CNOTs are needed. -/

/-- `addInPlace` whose bit-0 majority/erase pair is replaced by its two sum CNOTs. -/
def addLowNC (x y carry : List Wire) (cin : Wire) : Program :=
  addInPlace x.tail y.tail carry.tail cin ++ [.measureX (carry.headD 0) [] []] ++
    [.CX (x.headD 0) (y.headD 0), .CX cin (y.headD 0)]

theorem two_cx (a b cin : Wire) (t : State) (hab : a ≠ b) (hcb : cin ≠ b)
    (hc : t.basis cin = false) :
    run [.CX a b, .CX cin b] [] t = ⟨t.phase, writeBit t.basis b (t.basis b ^^ t.basis a)⟩ := by
  simp only [run]
  congr 1
  funext q
  by_cases hq : q = b
  · subst hq; simp [writeBit, Function.update, hcb, hc]
  · simp [writeBit, Function.update, hq]

theorem addLowNC_correct (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) (s : State) (m : List Bool)
    (hclean : ∀ w ∈ carry, s.basis w = false)
    (hnc : (s.basis (x.headD 0) && s.basis (y.headD 0)) = false) (hcin : s.basis cin = false) :
    (run (addLowNC x y carry cin) m s).phase = s.phase ∧
    (∀ w, w ∉ y → (run (addLowNC x y carry cin) m s).basis w = s.basis w) ∧
    regValue y (run (addLowNC x y carry cin) m s).basis =
      (regValue x s.basis + regValue y s.basis + (s.basis cin).toNat) % 2^y.length := by
  rcases x with _ | ⟨a, as⟩
  · simp at hx h2; omega
  rcases y with _ | ⟨b, bs⟩
  · simp at hx h2
  rcases carry with _ | ⟨c, cs⟩
  · simp only [List.length_cons, List.length_nil] at hc h2; omega
  · simp only [List.headD_cons] at hnc
    simp only [List.length_cons] at hx hc h2
    have hnd' : (cin :: (as ++ bs ++ cs)).Nodup := by
      apply List.Nodup.sublist _ hnd
      apply List.Sublist.cons₂
      simp only [List.cons_append, List.append_assoc]
      apply List.Sublist.cons
      apply List.Sublist.append_left
      apply List.Sublist.cons
      apply List.Sublist.append_left
      exact List.sublist_cons_self c cs
    have h0 := hnd
    simp only [List.cons_append, List.append_assoc, List.nodup_cons, List.mem_cons, List.mem_append,
      not_or] at h0
    have hca : cin ≠ a := h0.1.1
    have hcb : cin ≠ b := h0.1.2.2.1
    have hcinb : cin ∉ bs := h0.1.2.2.2.1
    have hab : a ≠ b := h0.2.1.2.1
    have ha : a ∉ bs := h0.2.1.2.2.1
    have hb : b ∉ bs := by
      have h := List.nodup_cons.mp hnd
      have h' := (List.nodup_append.mp (List.nodup_append.mp h.2).1).2.1
      exact (List.nodup_cons.mp h').1
    have hcy : c ∉ bs := by
      intro hc'
      have h := (List.nodup_cons.mp hnd).2
      rw [List.nodup_append] at h
      exact h.2.2 c (List.mem_append_right _ (List.mem_cons_of_mem b hc')) c List.mem_cons_self rfl
    have clean' : ∀ w ∈ cs, s.basis w = false := fun w hw => hclean w (List.mem_cons_of_mem c hw)
    have hframe : ∀ m', (run (addInPlace as bs cs cin) m' s).basis c = false := fun m' =>
      ((addInPlace_correct as bs cs cin hnd' (by omega) (by omega) s m' clean').2.1 c hcy).trans
        (hclean c List.mem_cons_self)
    have e : ∃ m1, run (addLowNC (a :: as) (b :: bs) (c :: cs) cin) m s =
        run [.CX a b, .CX cin b] [] (run (addInPlace as bs cs cin) m1 s) := by
      refine ⟨(m.take (measurementCount (addInPlace as bs cs cin ++ [.measureX c [] []]))).take
        (measurementCount (addInPlace as bs cs cin)), ?_⟩
      simp only [addLowNC, List.tail_cons, List.headD_cons]
      rw [run_append, run_append, measure_zero_id _ _ _ (hframe _)]
      rfl
    obtain ⟨m1, e⟩ := e
    have r := addInPlace_correct as bs cs cin hnd' (by omega) (by omega) s m1 clean'
    generalize ht : run (addInPlace as bs cs cin) m1 s = t at r e
    have ta : t.basis a = s.basis a := r.2.1 a ha
    have tb : t.basis b = s.basis b := r.2.1 b hb
    have tcin : t.basis cin = s.basis cin := r.2.1 cin hcinb
    rw [e, two_cx a b cin t hab hcb (tcin.trans hcin)]
    refine ⟨r.1, ?_, ?_⟩
    · intro w hw
      have wb : w ≠ b := fun e => hw (e ▸ List.mem_cons_self)
      simp only [writeBit, Function.update, wb, dite_false]
      exact r.2.1 w (fun h => hw (List.mem_cons_of_mem b h))
    · rw [foldr_cons_value, foldr_cons_value, foldr_cons_value]
      have rest : regValue bs (writeBit t.basis b (t.basis b ^^ t.basis a)) = regValue bs t.basis := by
        apply regValue_congr
        intro q hq
        have qb : q ≠ b := fun e => hb (e ▸ hq)
        simp [writeBit, Function.update, qb]
      rw [rest, r.2.2, ta, tb, hcin]
      simp only [writeBit, Function.update_self, Bool.toNat_false, Nat.add_zero, List.length_cons, pow_succ]
      have key : ∀ (u v : Bool) (A B : Nat), (u && v) = false →
          (if (v ^^ u) = true then 1 else 0) + 2 * ((A + B) % 2 ^ bs.length) =
            ((if u = true then 1 else 0) + 2 * A + ((if v = true then 1 else 0) + 2 * B)) % (2 ^ bs.length * 2) := by
        intro u v A B huv
        have hl := low_mod (if (v ^^ u) = true then 1 else 0) (A + B) bs.length (by split <;> omega)
        rw [hl]
        congr 1
        cases u <;> cases v <;> simp at huv ⊢ <;> ring
      exact key _ _ _ _ hnc

theorem addLowNC_counts (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    toffoliCount (addLowNC x y carry cin) + 1 = toffoliCount (addInPlace x y carry cin) ∧
    measurementCount (addLowNC x y carry cin) = measurementCount (addInPlace x y carry cin) := by
  have h := addInPlace_counts x.tail y.tail carry.tail cin
    (by simp only [List.length_tail]; omega) (by simp only [List.length_tail]; omega)
  have b := addInPlace_counts x y carry cin hx hc
  simp only [List.length_tail] at h
  simp only [addLowNC, toffoliCount_append, measurementCount_append, h.1, h.2, b.1, b.2]
  simp [toffoliCount, measurementCount]; omega

theorem addLowNC_wires_sub (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    wires (addLowNC x y carry cin) ⊆ wires (addInPlace x y carry cin) := by
  rw [addInPlace_wires x y carry cin hx hc]
  have base := addLow0_wires x y carry cin hx hc h2
  unfold addLow0 at base
  unfold addLowNC
  rw [wires_append]
  apply Finset.union_subset base
  rcases x with _ | ⟨a, as⟩
  · simp at hx; omega
  rcases y with _ | ⟨b, bs⟩
  · simp at hx h2
  intro q hq
  simp [wires, Instr.wires] at hq ⊢
  rcases hq with h | h | h <;> simp [h]

theorem addLowNC_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hx : 1 ≤ x.length) (hy : 1 ≤ y.length) :
    GatePhysical (addLowNC x y carry cin) := by
  have base := addLow0_physical x y carry cin hn
  unfold addLow0 at base
  unfold addLowNC
  rw [gatePhysical_append]
  refine ⟨base, ?_⟩
  rcases x with _ | ⟨a, as⟩
  · simp at hx
  rcases y with _ | ⟨b, bs⟩
  · simp at hy
  have h0 := hn
  simp only [List.cons_append, List.append_assoc, List.nodup_cons, List.mem_cons, List.mem_append,
    not_or] at h0
  intro i hi
  simp only [List.headD_cons, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact h0.2.1.2.1
  · exact h0.1.2.2.1

theorem addLowNC_slots (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    Challenge.gateSlots (addLowNC x y carry cin) ≤ Challenge.gateSlots (addInPlace x y carry cin) := by
  unfold addLowNC
  rw [Challenge.gateSlots_append, Challenge.gateSlots_append]
  have m1 : Challenge.gateSlots [Instr.measureX (carry.headD 0) [] []] = 1 := by
    simp [Challenge.gateSlots, Challenge.instructionSlots]
  have m2 : Challenge.gateSlots [Instr.CX (x.headD 0) (y.headD 0), Instr.CX cin (y.headD 0)] = 2 := by
    simp [Challenge.gateSlots, Challenge.instructionSlots]
  rw [m1, m2]
  rcases x with _ | ⟨a, _ | ⟨a', as⟩⟩
  · simp at hx; omega
  · simp at hx; omega
  rcases y with _ | ⟨b, _ | ⟨b', bs⟩⟩
  · simp at h2
  · simp at h2
  rcases carry with _ | ⟨c, cs⟩
  · simp at hc
  simp only [List.tail_cons, addInPlace, Challenge.gateSlots_append]
  rw [addInPlace_slots_cin (a' :: as) (b' :: bs) cs cin c]
  simp [Challenge.gateSlots, Challenge.instructionSlots, majority, eraseCarry]
  omega


/-- `subInPlace` with the bit-0 carry pair replaced: valid when `x₀ ∧ ¬y₀` is false. -/
def subLowNC (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addLowNC x y carry cin ++ notRegister y

theorem subLowNC_correct (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) (s : State) (m : List Bool)
    (hclean : ∀ q ∈ carry, s.basis q = false)
    (hnc : (s.basis (x.headD 0) && !s.basis (y.headD 0)) = false) (hcin : s.basis cin = false) :
    (run (subLowNC x y carry cin) m s).phase = s.phase ∧
    (∀ q, q ∉ y → (run (subLowNC x y carry cin) m s).basis q = s.basis q) ∧
    regValue y (run (subLowNC x y carry cin) m s).basis =
      (regValue y s.basis + 2^y.length - regValue x s.basis - (s.basis cin).toNat) % 2^y.length := by
  have words := List.nodup_cons.mp hn
  have split := List.nodup_append'.mp (show (x++(y++carry)).Nodup from by simpa only [List.append_assoc] using words.2)
  have nd := List.nodup_append'.mp split.2.1
  let u : State := ⟨s.phase, fun q => if q ∈ y then !s.basis q else s.basis q⟩
  have ci : cin ∉ y := fun h => words.1 (by simp [h])
  have clean : ∀ q ∈ carry, u.basis q = false := by
    intro q hq; have away : q ∉ y := fun h => List.disjoint_left.mp nd.2.2 h hq
    simp only [show u.basis q = s.basis q from by simp [u, away], hclean q hq]
  have source : regValue x u.basis = regValue x s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [u, show q ∉ y from fun h => List.disjoint_left.mp split.2.2 hq (by simp [h])])
  have input : regValue y u.basis = 2^y.length - 1 - regValue y s.basis := by
    rw [regValue_congr y _ (fun q => !s.basis q) (by intro q hq; simp [u, hq]), regValue_complement]
  have hx0 : u.basis (x.headD 0) = s.basis (x.headD 0) := by
    rcases x with _ | ⟨a, as⟩
    · simp at hx; omega
    · have : a ∉ y := fun h => List.disjoint_left.mp split.2.2 List.mem_cons_self (by simp [h])
      simp [u, this]
  have hy0 : u.basis (y.headD 0) = !s.basis (y.headD 0) := by
    rcases y with _ | ⟨b, bs⟩
    · simp at h2
    · simp [u]
  have add := addLowNC_correct x y carry cin hn hx hc h2 u m clean
    (by rw [hx0, hy0]; exact hnc) (by simp [u, ci, hcin])
  have sw := BalancedInverse.complement_sandwich y nd.1 (addLowNC x y carry cin)
    (regValue x s.basis) (s.basis cin).toNat s m
    (by simpa only [hx] using regValue_lt x s.basis) (by cases s.basis cin <;> decide)
    (by simpa only [source, input, show u.basis cin = s.basis cin from by simp [u, ci]] using add)
  simpa only [subLowNC, List.append_assoc] using sw

theorem subLowNC_counts (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    toffoliCount (subLowNC x y carry cin) + 1 = toffoliCount (subInPlace x y carry cin) ∧
    measurementCount (subLowNC x y carry cin) = measurementCount (subInPlace x y carry cin) := by
  have h := addLowNC_counts x y carry cin hx hc h2
  simp only [subLowNC, subInPlace, toffoliCount_append, measurementCount_append,
    (notRegister_counts y).1, (notRegister_counts y).2]
  omega

theorem subLowNC_wires_sub (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    wires (subLowNC x y carry cin) ⊆ wires (subInPlace x y carry cin) := by
  have h := addLowNC_wires_sub x y carry cin hx hc h2
  simp only [subLowNC, subInPlace, wires_append]
  intro q hq
  simp only [Finset.mem_union] at hq ⊢
  rcases hq with (h1 | h1) | h1
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (h h1))
  · exact Or.inr h1

theorem subLowNC_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hx : 1 ≤ x.length) (hy : 1 ≤ y.length) :
    GatePhysical (subLowNC x y carry cin) := by
  simp only [subLowNC, gatePhysical_append]
  exact ⟨⟨notRegister_physical _, addLowNC_physical x y carry cin hn hx hy⟩, notRegister_physical _⟩

theorem subLowNC_slots (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    Challenge.gateSlots (subLowNC x y carry cin) ≤ Challenge.gateSlots (subInPlace x y carry cin) := by
  have h := addLowNC_slots x y carry cin hx hc h2
  simp only [subLowNC, subInPlace, Challenge.gateSlots_append]
  omega


/-- The lowest wire of a nonempty register is its value's parity. -/
theorem head_bit (r tail : List Wire) (st : BasisState) (hne : r ≠ []) :
    st ((r ++ tail).headD 0) = decide (regValue r st % 2 = 1) := by
  match r, hne with
  | w :: ws, _ =>
    simp only [List.cons_append, List.headD_cons]
    rw [foldr_cons_value]
    by_cases hw : st w = true
    · rw [hw]; simp only [if_true]; simp
    · simp only [Bool.not_eq_true] at hw; rw [hw]; simp


/-! ### Guarded forms

The guarded programs fall back to the untrimmed adder when the register lengths are
degenerate, so their slot bound holds without any width hypothesis. -/

def addLow0G (x y carry : List Wire) (cin : Wire) : Program :=
  if x.length = y.length ∧ carry.length + 1 = y.length ∧ 2 ≤ y.length then addLow0 x y carry cin
  else addInPlace x y carry cin
def addLowNCG (x y carry : List Wire) (cin : Wire) : Program :=
  if x.length = y.length ∧ carry.length + 1 = y.length ∧ 2 ≤ y.length then addLowNC x y carry cin
  else addInPlace x y carry cin
def subLowNCG (x y carry : List Wire) (cin : Wire) : Program :=
  if x.length = y.length ∧ carry.length + 1 = y.length ∧ 2 ≤ y.length then subLowNC x y carry cin
  else subInPlace x y carry cin

theorem addLow0G_eq (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    addLow0G x y carry cin = addLow0 x y carry cin := if_pos ⟨hx, hc, h2⟩
theorem addLowNCG_eq (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    addLowNCG x y carry cin = addLowNC x y carry cin := if_pos ⟨hx, hc, h2⟩
theorem subLowNCG_eq (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    subLowNCG x y carry cin = subLowNC x y carry cin := if_pos ⟨hx, hc, h2⟩

theorem addLow0G_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addLow0G x y carry cin) ≤ Challenge.gateSlots (addInPlace x y carry cin) := by
  unfold addLow0G; split
  · next h => exact addLow0_slots x y carry cin h.1 h.2.1 h.2.2
  · exact le_refl _
theorem addLowNCG_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addLowNCG x y carry cin) ≤ Challenge.gateSlots (addInPlace x y carry cin) := by
  unfold addLowNCG; split
  · next h => exact addLowNC_slots x y carry cin h.1 h.2.1 h.2.2
  · exact le_refl _
theorem subLowNCG_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (subLowNCG x y carry cin) ≤ Challenge.gateSlots (subInPlace x y carry cin) := by
  unfold subLowNCG; split
  · next h => exact subLowNC_slots x y carry cin h.1 h.2.1 h.2.2
  · exact le_refl _

theorem addLow0G_wires_sub (x y carry : List Wire) (cin : Wire) :
    wires (addLow0G x y carry cin) ⊆ wires (addInPlace x y carry cin) := by
  unfold addLow0G; split
  · next h => exact addLow0_wires_sub x y carry cin h.1 h.2.1 h.2.2
  · exact subset_refl _
theorem addLowNCG_wires_sub (x y carry : List Wire) (cin : Wire) :
    wires (addLowNCG x y carry cin) ⊆ wires (addInPlace x y carry cin) := by
  unfold addLowNCG; split
  · next h => exact addLowNC_wires_sub x y carry cin h.1 h.2.1 h.2.2
  · exact subset_refl _
theorem subLowNCG_wires_sub (x y carry : List Wire) (cin : Wire) :
    wires (subLowNCG x y carry cin) ⊆ wires (subInPlace x y carry cin) := by
  unfold subLowNCG; split
  · next h => exact subLowNC_wires_sub x y carry cin h.1 h.2.1 h.2.2
  · exact subset_refl _

theorem nodup_assoc (cin : Wire) (x y carry : List Wire) (hn : (cin :: (x ++ y ++ carry)).Nodup) :
    (cin :: x ++ y ++ carry).Nodup := by
  simpa only [List.cons_append, List.append_assoc] using hn

theorem addLow0G_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) : GatePhysical (addLow0G x y carry cin) := by
  unfold addLow0G; split
  · exact addLow0_physical x y carry cin hn
  · exact addInPlace_physical x y carry cin (nodup_assoc cin x y carry hn)
theorem addLowNCG_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) : GatePhysical (addLowNCG x y carry cin) := by
  unfold addLowNCG; split
  · next h => exact addLowNC_physical x y carry cin hn (by omega) (by omega)
  · exact addInPlace_physical x y carry cin (nodup_assoc cin x y carry hn)
theorem subLowNCG_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) : GatePhysical (subLowNCG x y carry cin) := by
  unfold subLowNCG; split
  · next h => exact subLowNC_physical x y carry cin hn (by omega) (by omega)
  · simp only [subInPlace, gatePhysical_append]
    exact ⟨⟨notRegister_physical _, addInPlace_physical x y carry cin (nodup_assoc cin x y carry hn)⟩,
      notRegister_physical _⟩

end ECDSAAdd.Entrant.LowZero
