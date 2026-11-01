import ECDSAAdd.Submission.Entrant.MainB
import ECDSAAdd.Submission.Entrant.TrimRow
import ECDSAAdd.Submission.Entrant.TrimSq3
import ECDSAAdd.Submission.Entrant.MeasuredZeroClear
import ECDSAAdd.Submission.Entrant.MeasuredDH

-- ===== ECDSAAdd.Submission.Entrant.LowZero =====
section
-- consolidated import: import ECDSAAdd.Arithmetic.InPlaceAdder
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.Registers
-- consolidated import: import ECDSAAdd.Baselines.SlotMapped
-- consolidated import: import ECDSAAdd.Arithmetic.BalancedFieldInverseArithmetic

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

end ECDSAAdd.Entrant.LowZero
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18KRegs =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.DiagSquare
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero

/-! The LowZero wrappers from accepted606afa1e, with the checked old KRegs layout. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic
variable (R : KRegs)

/-- `m8` with the dead lowest carry dropped: its source `T = 2ab` is even and `cin` is clean. -/
def m8z : Program := LowZero.addLow0 (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin

theorem m8z_lens (w : R.W) : (R.T++R.zM).length=R.dmid.length ∧
    (R.carry.take (R.dmid.length-1)).length+1=R.dmid.length ∧ 2≤R.dmid.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega

theorem m8z_counts (w : R.W) : toffoliCount R.m8z+1=toffoliCount R.m8 ∧
    measurementCount R.m8z=measurementCount R.m8 := by
  have l := R.m8z_lens w
  exact LowZero.addLow0_counts_rel _ _ _ _ l.1 l.2.1 l.2.2

theorem m8z_wires (w : R.W) : wires R.m8z⊆wires R.m8 := by
  have l := R.m8z_lens w
  exact LowZero.addLow0_wires_sub _ _ _ _ l.1 l.2.1 l.2.2

theorem m8z_slots (w : R.W) : Challenge.gateSlots R.m8z≤Challenge.gateSlots R.m8 := by
  have l := R.m8z_lens w
  exact LowZero.addLow0_slots _ _ _ _ l.1 l.2.1 l.2.2

theorem m8z_physical (hn : R.all.Nodup) : GatePhysical R.m8z :=
  LowZero.addLow0_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))

theorem m8z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (k : Nat)
    (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hT : regValue R.T s.basis=2*k) (hi : s.basis R.cin=false) :
    (run R.m8z m s).phase=s.phase ∧
    (∀q,q∉R.dmid → (run R.m8z m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.m8z m s).basis=
      (regValue (R.T++R.zM) s.basis+regValue R.dmid s.basis+(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8z_lens w
  have hTl := w.T; have hSl := w.S
  have ne : R.T≠[] := by
    intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
  exact LowZero.addLow0_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl (LowZero.head_false_of_even R.T R.zM s.basis k hT ne) hi

/-- `m7` (`T -= b²`) with its dead lowest carry dropped: bit 0 of `T = 2ab+b²` equals bit 0 of `b²`. -/
def m7z : Program := LowZero.subLowNC (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
/-- `c8` (`dmid -= T`) with its dead lowest carry dropped: `T = 2ab` is even. -/
def c8z : Program := LowZero.subLowNC (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
/-- `c7` (`T += b²`) with its dead lowest carry dropped: `T = 2ab` is even. -/
def c7z : Program := LowZero.addLowNC (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin

theorem t_lens (w : R.W) : (R.dhi++R.zB).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length ∧ 1≤(R.dhi++R.zB).length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
  · simp only [List.length_append]; omega

theorem T_ne (w : R.W) : R.T≠[] := by
  have hTl := w.T; have hSl := w.S
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega

theorem dhi_ne (w : R.W) : R.dhi≠[] := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega

theorem m7z_counts (w : R.W) : toffoliCount R.m7z+1=toffoliCount R.m7 ∧
    measurementCount R.m7z=measurementCount R.m7 := by
  have l := R.t_lens w
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7z_counts (w : R.W) : toffoliCount R.c7z+1=toffoliCount R.c7 ∧
    measurementCount R.c7z=measurementCount R.c7 := by
  have l := R.t_lens w
  exact LowZero.addLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c8z_counts (w : R.W) : toffoliCount R.c8z+1=toffoliCount R.c8 ∧
    measurementCount R.c8z=measurementCount R.c8 := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2

theorem m7z_wires (w : R.W) : wires R.m7z⊆wires R.m7 := by
  have l := R.t_lens w
  exact LowZero.subLowNC_wires_sub _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7z_wires (w : R.W) : wires R.c7z⊆wires R.c7 := by
  have l := R.t_lens w
  exact LowZero.addLowNC_wires_sub _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c8z_wires (w : R.W) : wires R.c8z⊆wires R.c8 := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_wires_sub _ _ _ _ l.1 l.2.1 l.2.2

theorem m7z_slots (w : R.W) : Challenge.gateSlots R.m7z≤Challenge.gateSlots R.m7 := by
  have l := R.t_lens w
  exact LowZero.subLowNC_slots _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7z_slots (w : R.W) : Challenge.gateSlots R.c7z≤Challenge.gateSlots R.c7 := by
  have l := R.t_lens w
  exact LowZero.addLowNC_slots _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c8z_slots (w : R.W) : Challenge.gateSlots R.c8z≤Challenge.gateSlots R.c8 := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_slots _ _ _ _ l.1 l.2.1 l.2.2

theorem m7z_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.m7z := by
  have l := R.t_lens w
  exact LowZero.subLowNC_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) l.2.2.2 (by omega)
theorem c7z_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.c7z := by
  have l := R.t_lens w
  exact LowZero.addLowNC_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) l.2.2.2 (by omega)
theorem c8z_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.c8z := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) (by omega) (by omega)

theorem m7z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.m7z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m7z m s).basis q=s.basis q) ∧
    regValue R.T (run R.m7z m s).basis=
      (regValue R.T s.basis+2^R.T.length-regValue (R.dhi++R.zB) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lens w
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi
theorem c8z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hnc : (s.basis ((R.T++R.zM).headD 0) && !s.basis (R.dmid.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c8z m s).phase=s.phase ∧ (∀q,q∉R.dmid → (run R.c8z m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.c8z m s).basis=
      (regValue R.dmid s.basis+2^R.dmid.length-regValue (R.T++R.zM) s.basis-(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl hnc hi
theorem c7z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c7z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c7z m s).basis q=s.basis q) ∧
    regValue R.T (run R.c7z m s).basis=
      (regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lens w
  exact LowZero.addLowNC_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi


end ECDSAAdd.Entrant.KRegs
end -- original module boundary


section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero
open ECDSAAdd ECDSAAdd.Arithmetic
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

namespace ECDSAAdd.Entrant.KRegs
open Arithmetic
variable (R : KRegs)
/-! Low-bit carry trims (LowZero): each `*z` program drops the dead bit-0 carry of the
corresponding Karatsuba combination adder. -/
theorem m8g_lens (w : R.W) : (R.T++R.zM).length=R.dmid.length ∧
    (R.carry.take (R.dmid.length-1)).length+1=R.dmid.length ∧ 2≤R.dmid.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
theorem t_lensg (w : R.W) : (R.dhi++R.zB).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length ∧ 1≤(R.dhi++R.zB).length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
  · simp only [List.length_append]; omega
theorem lo_lens (w : R.W) : (R.dlo++R.zA).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length ∧ 1≤(R.dlo++R.zA).length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
  · simp only [List.length_append]; omega
theorem T_neg (w : R.W) : R.T≠[] := by
  have hTl := w.T; have hSl := w.S
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
theorem dhi_neg (w : R.W) : R.dhi≠[] := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
theorem dlo_ne (w : R.W) : R.dlo≠[] := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
def m8g : Program := LowZero.addLow0G (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
theorem m8g_counts (w : R.W) : toffoliCount R.m8g+1=toffoliCount R.m8 ∧
    measurementCount R.m8g=measurementCount R.m8 := by
  have l := R.m8g_lens w
  unfold m8g; rw [LowZero.addLow0G_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.addLow0_counts_rel _ _ _ _ l.1 l.2.1 l.2.2
theorem m8g_wires : wires R.m8g⊆wires R.m8 := LowZero.addLow0G_wires_sub _ _ _ _
theorem m8g_slots : Challenge.gateSlots R.m8g≤Challenge.gateSlots R.m8 := LowZero.addLow0G_slots _ _ _ _
theorem m8g_physical (hn : R.all.Nodup) : GatePhysical R.m8g :=
  LowZero.addLow0G_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem m8g_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (k : Nat) (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hT : regValue R.T s.basis=2*k) (hi : s.basis R.cin=false) :
    (run R.m8g m s).phase=s.phase ∧ (∀q,q∉R.dmid → (run R.m8g m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.m8g m s).basis=(regValue (R.T++R.zM) s.basis+regValue R.dmid s.basis+(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8g_lens w
  unfold m8g; rw [LowZero.addLow0G_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.addLow0_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl (LowZero.head_false_of_even R.T R.zM s.basis k hT (R.T_neg w)) hi

def m7g : Program := LowZero.subLowNCG (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
theorem m7g_counts (w : R.W) : toffoliCount R.m7g+1=toffoliCount R.m7 ∧
    measurementCount R.m7g=measurementCount R.m7 := by
  have l := R.t_lensg w
  unfold m7g; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem m7g_wires : wires R.m7g⊆wires R.m7 := LowZero.subLowNCG_wires_sub _ _ _ _
theorem m7g_slots : Challenge.gateSlots R.m7g≤Challenge.gateSlots R.m7 := LowZero.subLowNCG_slots _ _ _ _
theorem m7g_physical (hn : R.all.Nodup) : GatePhysical R.m7g :=
  LowZero.subLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem m7g_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.m7g m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m7g m s).basis q=s.basis q) ∧
    regValue R.T (run R.m7g m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dhi++R.zB) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lensg w
  unfold m7g; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

def c8g : Program := LowZero.subLowNCG (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
theorem c8g_counts (w : R.W) : toffoliCount R.c8g+1=toffoliCount R.c8 ∧
    measurementCount R.c8g=measurementCount R.c8 := by
  have l := R.m8g_lens w
  unfold c8g; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2
theorem c8g_wires : wires R.c8g⊆wires R.c8 := LowZero.subLowNCG_wires_sub _ _ _ _
theorem c8g_slots : Challenge.gateSlots R.c8g≤Challenge.gateSlots R.c8 := LowZero.subLowNCG_slots _ _ _ _
theorem c8g_physical (hn : R.all.Nodup) : GatePhysical R.c8g :=
  LowZero.subLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem c8g_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hnc : (s.basis ((R.T++R.zM).headD 0) && !s.basis (R.dmid.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c8g m s).phase=s.phase ∧ (∀q,q∉R.dmid → (run R.c8g m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.c8g m s).basis=(regValue R.dmid s.basis+2^R.dmid.length-regValue (R.T++R.zM) s.basis-(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8g_lens w
  unfold c8g; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl hnc hi

def c7g : Program := LowZero.addLowNCG (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
theorem c7g_counts (w : R.W) : toffoliCount R.c7g+1=toffoliCount R.c7 ∧
    measurementCount R.c7g=measurementCount R.c7 := by
  have l := R.t_lensg w
  unfold c7g; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7g_wires : wires R.c7g⊆wires R.c7 := LowZero.addLowNCG_wires_sub _ _ _ _
theorem c7g_slots : Challenge.gateSlots R.c7g≤Challenge.gateSlots R.c7 := LowZero.addLowNCG_slots _ _ _ _
theorem c7g_physical (hn : R.all.Nodup) : GatePhysical R.c7g :=
  LowZero.addLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem c7g_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c7g m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c7g m s).basis q=s.basis q) ∧
    regValue R.T (run R.c7g m s).basis=(regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lensg w
  unfold c7g; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

def m6z : Program := LowZero.subLowNCG (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
theorem m6z_counts (w : R.W) : toffoliCount R.m6z+1=toffoliCount R.m6 ∧
    measurementCount R.m6z=measurementCount R.m6 := by
  have l := R.lo_lens w
  unfold m6z; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem m6z_wires : wires R.m6z⊆wires R.m6 := LowZero.subLowNCG_wires_sub _ _ _ _
theorem m6z_slots : Challenge.gateSlots R.m6z≤Challenge.gateSlots R.m6 := LowZero.subLowNCG_slots _ _ _ _
theorem m6z_physical (hn : R.all.Nodup) : GatePhysical R.m6z :=
  LowZero.subLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem m6z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.m6z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m6z m s).basis q=s.basis q) ∧
    regValue R.T (run R.m6z m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dlo++R.zA) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.lo_lens w
  unfold m6z; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

def c6z : Program := LowZero.addLowNCG (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
theorem c6z_counts (w : R.W) : toffoliCount R.c6z+1=toffoliCount R.c6 ∧
    measurementCount R.c6z=measurementCount R.c6 := by
  have l := R.lo_lens w
  unfold c6z; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c6z_wires : wires R.c6z⊆wires R.c6 := LowZero.addLowNCG_wires_sub _ _ _ _
theorem c6z_slots : Challenge.gateSlots R.c6z≤Challenge.gateSlots R.c6 := LowZero.addLowNCG_slots _ _ _ _
theorem c6z_physical (hn : R.all.Nodup) : GatePhysical R.c6z :=
  LowZero.addLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem c6z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c6z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c6z m s).basis q=s.basis q) ∧
    regValue R.T (run R.c6z m s).basis=(regValue (R.dlo++R.zA) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.lo_lens w
  unfold c6z; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

end ECDSAAdd.Entrant.KRegs

namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-- `rawMake` with the dead lowest carry of the first signed row copied (TrimRow). -/
def rawMakeT (xs dst pad carry : List Wire) : Program := ECDSAAdd.Entrant.TrimRow.mk xs dst pad carry

/-- `rawClear` with the dead lowest carry of the first signed row copied (TrimRow). -/
def rawClearT (xs dst pad carry : List Wire) : Program := ECDSAAdd.Entrant.TrimRow.cl xs dst pad carry

theorem rawMakeT_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawMakeT xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawMakeT xs dst pad carry) m s).basis=
      (regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length ∧
    ∀q,q∉dst → (run (rawMakeT xs dst pad carry) m s).basis q=s.basis q := by
  obtain ⟨R,hR⟩ := ECDSAAdd.Entrant.TrimRow.mk_exists xs dst pad carry hn hx hd hp hc s m h0 hc0
  rw [rawMakeT,hR]
  exact rawMake_correct xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0

theorem rawClearT_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool)
    (h0 : regValue dst s.basis=(regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawClearT xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawClearT xs dst pad carry) m s).basis=0 ∧
    ∀q,q∉dst → (run (rawClearT xs dst pad carry) m s).basis q=s.basis q := by
  obtain ⟨R,hR⟩ := ECDSAAdd.Entrant.TrimRow.cl_exists xs dst pad carry hn hx hd hp hc s m h0 hc0
  rw [rawClearT,hR]
  exact rawClear_correct xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0

theorem rawT_counts (xs dst pad carry : List Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : xs.length-1≤carry.length) :
    (toffoliCount (rawMakeT xs dst pad carry)+1=toffoliCount (rawMake xs dst pad carry) ∧
      measurementCount (rawMakeT xs dst pad carry)+1=measurementCount (rawMake xs dst pad carry)) ∧
    (toffoliCount (rawClearT xs dst pad carry)+1=toffoliCount (rawClear xs dst pad carry) ∧
      measurementCount (rawClearT xs dst pad carry)+1=measurementCount (rawClear xs dst pad carry)) :=
  ECDSAAdd.Entrant.TrimRow.counts xs dst pad carry hx hd hp hc

theorem rawT_slots (xs dst pad carry : List Wire) :
    Challenge.gateSlots (rawMakeT xs dst pad carry)≤Challenge.gateSlots (rawMake xs dst pad carry) ∧
    Challenge.gateSlots (rawClearT xs dst pad carry)≤Challenge.gateSlots (rawClear xs dst pad carry) :=
  ECDSAAdd.Entrant.TrimRow.slots xs dst pad carry

theorem rawT_wires (xs dst pad carry : List Wire) (X : Finset Wire)
    (h1 : wires (signedSquareRows xs dst pad carry)⊆X) (h2 : wires (signedSquareTop xs dst)⊆X)
    (h3 : wires (signedSquareRowsClear xs dst pad carry)⊆X) :
    wires (rawMakeT xs dst pad carry)⊆X ∧ wires (rawClearT xs dst pad carry)⊆X := by
  have w := ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry
  simp only [wires_append] at w
  exact ⟨w.1.trans (Finset.union_subset h1 h2),w.2.trans (Finset.union_subset h2 h3)⟩

theorem rawT_physical (xs dst pad carry : List Wire)
    (h1 : GatePhysical (signedSquareRows xs dst pad carry)) (h2 : GatePhysical (signedSquareTop xs dst))
    (h3 : GatePhysical (signedSquareRowsClear xs dst pad carry)) :
    GatePhysical (rawMakeT xs dst pad carry) ∧ GatePhysical (rawClearT xs dst pad carry) :=
  ECDSAAdd.Entrant.TrimRow.physical xs dst pad carry
    (by rw [gatePhysical_append]; exact ⟨h1,h2⟩) (by rw [gatePhysical_append]; exact ⟨h2,h3⟩)


def seedsT (R : KRegs) : Program :=
  rawMakeT R.lo R.dlo R.pad R.carry ++ rawMakeT R.hi R.dhi R.pad R.carry ++ R.smk ++
    rawMakeT R.S R.T R.pad R.carry

theorem seedsT_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (seedsT R) m s)
      (vec (rawValue R.h (regValue R.lo s.basis)) (rawValue R.h (regValue R.hi s.basis))
        (regValue R.lo s.basis+regValue R.hi s.basis)
        (rawValue (R.h+1) (regValue R.lo s.basis+regValue R.hi s.basis))) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry; have hpl := w.pad
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  have init : Shape R s s (vec 0 0 0 0) := by
    refine ⟨rfl,?_,fun _ _ _ _ => rfl⟩
    intro i; fin_cases i
    · change (regValue R.dlo s.basis : Int) ≡ 0 [ZMOD _]
      rw [KRegs.xz (r:=R.dlo) hd0 (fun q h => List.mem_of_mem_take h)]; rfl
    · change (regValue R.dhi s.basis : Int) ≡ 0 [ZMOD _]
      rw [KRegs.xz (r:=R.dhi) hd0 (fun q h => List.mem_of_mem_drop h)]; rfl
    · change (regValue R.S s.basis : Int) ≡ 0 [ZMOD _]
      rw [hS0]; rfl
    · change (regValue R.T s.basis : Int) ≡ 0 [ZMOD _]
      rw [hT0]; rfl
  have loStep : Transition R s (vec 0 0 0 0) (vec (rawValue R.h a) 0 0 0)
      (rawMakeT R.lo R.dlo R.pad R.carry) := by
    intro t rec ht
    have lt := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
    have r := rawMakeT_correct R.lo R.dlo R.pad R.carry
      (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
      (by omega) (by omega) hpl (by omega) t rec
      (ht.exact 0 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 0) (run (rawMakeT R.lo R.dlo R.pad R.carry) rec t).basis : Int) ≡
        (rawValue R.h a : Nat) [ZMOD (2^(reg R 0).length : Nat)] := by
      change (regValue R.dlo _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,lt,L0]; rfl
    simpa only [vec0] using ht.step hn 0 (rawValue R.h a) r.1 r.2.2 v
  have hiStep : Transition R s (vec (rawValue R.h a) 0 0 0)
      (vec (rawValue R.h a) (rawValue R.h b) 0 0) (rawMakeT R.hi R.dhi R.pad R.carry) := by
    intro t rec ht
    have ht0 := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
    have r := rawMakeT_correct R.hi R.dhi R.pad R.carry
      (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
      (by omega) (by omega) hpl (by omega) t rec
      (ht.exact 1 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 1) (run (rawMakeT R.hi R.dhi R.pad R.carry) rec t).basis : Int) ≡
        (rawValue R.h b : Nat) [ZMOD (2^(reg R 1).length : Nat)] := by
      change (regValue R.dhi _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,ht0,hhi]; rfl
    simpa only [vec1] using ht.step hn 1 (rawValue R.h b) r.1 r.2.2 v
  have sumStep : Transition R s (vec (rawValue R.h a) (rawValue R.h b) 0 0)
      (vec (rawValue R.h a) (rawValue R.h b) (a+b) 0) R.smk := by
    intro t rec ht
    have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
    have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
    have r := R.smk_correct w hn t rec (ht.exact 2 0 rfl (by norm_num))
      ((ht.keep hn R.z (by intro q h; simp [h])).trans hz0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0) ((ht.cin hn).trans hi0)
    have v : (regValue (reg R 2) (run R.smk rec t).basis : Int) ≡ (a+b : Nat) [ZMOD (2^(reg R 2).length : Nat)] := by
      change (regValue R.S _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,al,bl]
    simpa only [vec2] using ht.step hn 2 (a+b : Nat) r.1 r.2.2 v
  have sqStep : Transition R s (vec (rawValue R.h a) (rawValue R.h b) (a+b) 0)
      (vec (rawValue R.h a) (rawValue R.h b) (a+b) (rawValue (R.h+1) (a+b)))
      (rawMakeT R.S R.T R.pad R.carry) := by
    intro t rec ht
    have av := regValue_lt R.lo s.basis
    have bv := regValue_lt R.hi s.basis
    rw [L0] at av; rw [hhi] at bv
    have slt : a+b<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [a,b]; omega
    have sv := ht.exact 2 (a+b) rfl slt
    change regValue R.S t.basis=a+b at sv
    have r := rawMakeT_correct R.S R.T R.pad R.carry
      (knd hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega))
      (by omega) hTl hpl (by omega) t rec
      (ht.exact 3 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 3) (run (rawMakeT R.S R.T R.pad R.carry) rec t).basis : Int) ≡
        (rawValue (R.h+1) (a+b) : Nat) [ZMOD (2^(reg R 3).length : Nat)] := by
      change (regValue R.T _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,sv,hSS]; rfl
    simpa only [vec3] using ht.step hn 3 (rawValue (R.h+1) (a+b)) r.1 r.2.2 v
  exact (((loStep.seq hiStep).seq sumStep).seq sqStep) s m init



theorem rawClearT_wires_sub (xs dst pad carry : List Wire) :
    wires (rawClearT xs dst pad carry)⊆wires (rawClear xs dst pad carry) := by
  unfold rawClearT rawClear; exact (ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry).2
theorem rawClearT_slots_le (xs dst pad carry : List Wire) :
    Challenge.gateSlots (rawClearT xs dst pad carry)≤Challenge.gateSlots (rawClear xs dst pad carry) := by
  unfold rawClearT rawClear; exact (ECDSAAdd.Entrant.TrimRow.slots xs dst pad carry).2
theorem rawClearT_physical_of (xs dst pad carry : List Wire) (hm : GatePhysical (rawMake xs dst pad carry))
    (hc : GatePhysical (rawClear xs dst pad carry)) : GatePhysical (rawClearT xs dst pad carry) := by
  unfold rawClearT; exact (ECDSAAdd.Entrant.TrimRow.physical xs dst pad carry hm hc).2
theorem rawClearT_counts (xs dst pad carry : List Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length) :
    toffoliCount (rawClearT xs dst pad carry)+1=toffoliCount (rawClear xs dst pad carry) ∧
      measurementCount (rawClearT xs dst pad carry)+1=measurementCount (rawClear xs dst pad carry) :=
  (rawT_counts xs dst pad carry hx hd hp hc).2

theorem rawclearlo_transitionT (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hp0 : regValue R.pad base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (B S T : Int) :
    Transition R base (vec (rawValue R.h (regValue R.lo base.basis)) B S T) (vec 0 B S T) (rawClearT R.lo R.dlo R.pad R.carry) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry; have hpl := w.pad
  have hlen : R.lo.length=R.h := by omega
  have hdlen : R.dlo.length=2*R.h := by omega
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have rb := rawValue_bound R.lo base.basis (by omega)
  rw [hlen] at rb
  have dv := ht.exact 0 (rawValue R.h (regValue R.lo base.basis)) rfl
    (by change _<2^R.dlo.length; rw [hdlen]; exact rb)
  change regValue R.dlo t.basis=_ at dv
  have r := rawClearT_correct R.lo R.dlo R.pad R.carry
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) hpl (by omega) t rec (by rw [xv,hlen]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 0) (run (rawClearT R.lo R.dlo R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 0).length : Nat)] := by
    change (regValue R.dlo _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec0] using ht.step hn 0 0 r.1 r.2.2 val

theorem rawclearhi_transitionT (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hp0 : regValue R.pad base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (A S T : Int) :
    Transition R base (vec A (rawValue R.h (regValue R.hi base.basis)) S T) (vec A 0 S T) (rawClearT R.hi R.dhi R.pad R.carry) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry; have hpl := w.pad
  have hlen : R.hi.length=R.h := by omega
  have hdlen : R.dhi.length=2*R.h := by omega
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have rb := rawValue_bound R.hi base.basis (by omega)
  rw [hlen] at rb
  have dv := ht.exact 1 (rawValue R.h (regValue R.hi base.basis)) rfl
    (by change _<2^R.dhi.length; rw [hdlen]; exact rb)
  change regValue R.dhi t.basis=_ at dv
  have r := rawClearT_correct R.hi R.dhi R.pad R.carry
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) hpl (by omega) t rec (by rw [xv,hlen]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 1) (run (rawClearT R.hi R.dhi R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 1).length : Nat)] := by
    change (regValue R.dhi _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec1] using ht.step hn 1 0 r.1 r.2.2 val

theorem rawclearSum_transitionT (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hp0 : regValue R.pad base.basis=0) (hc0 : regValue R.carry base.basis=0)
    (A B : Int) (S : Nat) (hS : S<2^R.S.length) :
    Transition R base (vec A B S (rawValue R.S.length S)) (vec A B S 0)
      (rawClearT R.S R.T R.pad R.carry) := by
  intro t rec ht
  have h4 := w.h4; have hh := w.hh; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hpl := w.pad
  have sv := ht.exact 2 S rfl hS
  change regValue R.S t.basis=S at sv
  have rb := rawValue_bound R.S t.basis (by omega)
  rw [sv] at rb
  have dv := ht.exact 3 (rawValue R.S.length S) rfl (by change _<2^R.T.length; rw [htl]; exact rb)
  change regValue R.T t.basis=_ at dv
  have r := rawClearT_correct R.S R.T R.pad R.carry
    (knd hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega))
    (by omega) htl hpl (by omega) t rec (by rw [sv]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 3) (run (rawClearT R.S R.T R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 3).length : Nat)] := by
    change (regValue R.T _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec3] using ht.step hn 3 0 r.1 r.2.2 val

end ECDSAAdd.Entrant.DiagSq

section
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-! Constant `+1` on the top three bits with a clean carry-in: the bit-0 majority of a
constant-one bit is `[CX y c, CX cin c, CCX y cin c]`, and its Toffoli is the identity
while `cin = 0`. `incr1` drops it. -/

theorem ccx_noop (a b t : Wire) (p : Program) (m : List Bool) (s : State) (h : s.basis b=false) :
    run (.CCX a b t :: p) m s=run p m s := by
  have e : (⟨s.phase,writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))⟩ : State)=s := by
    obtain ⟨ph,bs⟩ := s
    simp only at h
    congr 1
    funext q
    by_cases hq : q=t
    · subst hq; simp [writeBit,h]
    · simp [writeBit,Function.update,hq]
  simp only [run]
  rw [e]

theorem run_cx_cx_ccx (y cin c : Wire) (X : Program) (m : List Bool) (s : State)
    (hi : s.basis cin=false) (hcc : cin≠c) :
    run (.CX y c :: .CX cin c :: .CCX y cin c :: X) m s=run (.CX y c :: .CX cin c :: X) m s := by
  let t1 : State := ⟨s.phase,writeBit s.basis c (s.basis c ^^ s.basis y)⟩
  let t2 : State := ⟨t1.phase,writeBit t1.basis c (t1.basis c ^^ t1.basis cin)⟩
  have ht2 : t2.basis cin=false := by
    simp [t2,t1,writeBit,Function.update,hcc,hi]
  calc run (.CX y c :: .CX cin c :: .CCX y cin c :: X) m s=run (.CCX y cin c :: X) m t2 := rfl
    _=run X m t2 := ccx_noop _ _ _ _ _ _ ht2
    _=run (.CX y c :: .CX cin c :: X) m s := rfl

def incr1 (ys carry : List Wire) (cin : Wire) : Program :=
  match ys, carry with
  | y::y'::ys', c::cs => [.CX y c,.CX cin c]++mappedAdd (mappedConstant none 2 0) (y'::ys') cs c++
      mappedEraseCarry (mappedConstantBit none true) y cin c++mappedSum (mappedConstantBit none true) y cin
  | _, _ => mappedAdd (mappedConstant none 3 1) ys carry cin

theorem incr1_split (y y' c cin : Wire) (ys cs : List Wire) :
    mappedAdd (mappedConstant none 3 1) (y::y'::ys) (c::cs) cin=
      [.CX y c,.CX cin c,.CCX y cin c]++(mappedAdd (mappedConstant none 2 0) (y'::ys) cs c++
      mappedEraseCarry (mappedConstantBit none true) y cin c++mappedSum (mappedConstantBit none true) y cin) := by
  simp [mappedConstant,mappedAdd,mappedMajority,mappedConstantBit,List.append_assoc]

theorem incr1_run (ys carry : List Wire) (cin : Wire) (s : State) (m : List Bool)
    (hi : s.basis cin=false) (hc : ∀c∈carry.take 1,cin≠c) :
    run (incr1 ys carry cin) m s=run (mappedAdd (mappedConstant none 3 1) ys carry cin) m s := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try rfl
  have hcc : cin≠c := hc c (by simp)
  rw [incr1_split]
  simp only [incr1,List.append_assoc,List.cons_append,List.nil_append]
  exact (run_cx_cx_ccx y cin c _ m s hi hcc).symm

theorem incr1_mc (ys carry : List Wire) (cin : Wire) :
    measurementCount (incr1 ys carry cin)=measurementCount (mappedAdd (mappedConstant none 3 1) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> rfl

def decr1 (ys carry : List Wire) (cin : Wire) : Program :=
  notRegister ys++incr1 ys carry cin++notRegister ys

theorem decr1_run (ys carry : List Wire) (cin : Wire) (s : State) (m : List Bool)
    (hi : s.basis cin=false) (hc : ∀c∈carry.take 1,cin≠c) (hy : cin∉ys) (hyn : ys.Nodup) :
    run (decr1 ys carry cin) m s=run (mappedSub (mappedConstant none 3 1) ys carry cin) m s := by
  have hm : measurementCount (notRegister ys)=0 := (notRegister_counts ys).2
  have nr := notRegister_correct ys hyn s []
  simp only [decr1,mappedSub,List.append_assoc]
  rw [run_append (notRegister ys),run_append (notRegister ys),hm]
  simp only [List.take_zero,List.drop_zero]
  rw [run_append (incr1 ys carry cin),run_append (mappedAdd (mappedConstant none 3 1) ys carry cin),incr1_mc,
    incr1_run ys carry cin _ _ (by rw [nr]; simp [hy,hi]) hc]

theorem incr1_mem (ys carry : List Wire) (cin : Wire) :
    ∀i∈incr1 ys carry cin,i∈mappedAdd (mappedConstant none 3 1) ys carry cin := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try (intro i h; exact h)
  rw [incr1_split]
  intro i h
  simp only [incr1,List.mem_append,List.mem_cons] at h ⊢
  tauto

theorem incr1_counts (ys carry : List Wire) (cin : Wire) (h2 : 2≤ys.length) (hc : 1≤carry.length) :
    toffoliCount (incr1 ys carry cin)+1=toffoliCount (mappedAdd (mappedConstant none 3 1) ys carry cin) ∧
    measurementCount (incr1 ys carry cin)=measurementCount (mappedAdd (mappedConstant none 3 1) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> simp at h2 hc
  rw [incr1_split]
  simp only [incr1,toffoliCount_append,measurementCount_append]
  simp [toffoliCount,measurementCount]
  omega

theorem incr1_slots (ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (incr1 ys carry cin)≤Challenge.gateSlots (mappedAdd (mappedConstant none 3 1) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try exact le_refl _
  rw [incr1_split]
  simp only [incr1,Challenge.gateSlots_append]
  simp [Challenge.gateSlots,Challenge.instructionSlots]
  omega

theorem wires_of_mem {p q : Program} (h : ∀i∈p,i∈q) : wires p⊆wires q := by
  induction p with
  | nil => simp [wires]
  | cons i p ih =>
    simp only [wires]
    apply Finset.union_subset
    · intro w hw
      have hq := h i (by simp)
      clear h ih
      induction q with
      | nil => simp at hq
      | cons j q ihq =>
        simp only [wires,Finset.mem_union]
        rcases List.mem_cons.mp hq with e|e
        · subst e; exact Or.inl hw
        · exact Or.inr (ihq e)
    · exact ih (fun j hj => h j (by simp [hj]))

def correctionZ (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire) : Program :=
  loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h ++
    incr1 (dst.drop (2*h-1)) (carry.take 2) cin

def correctionBackZ (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire) : Program :=
  decr1 (dst.drop (2*h-1)) (carry.take 2) cin ++
  loadedAdd (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h

theorem correctionZ_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (-((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)+
      (2^(2*h-1) : Nat)) s (run (correctionZ h as bs ss dst carry q cin) m s) := by
  let P := loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h
  have r := sharedSub_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s
    (m.take (measurementCount P)) hv hq0 hi0 hc0
  have out (w : Wire) (hw : w∈cin::carry) : w∉dst :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have ui : (run P (m.take (measurementCount P)) s).basis cin=false := (r.2.1 cin (out cin (by simp))).trans hi0
  have hc : ∀c∈(carry.take 2).take 1,cin≠c := by
    intro c hc e; subst e
    have := List.mem_of_mem_take (List.mem_of_mem_take hc)
    have h0 := (List.nodup_cons.mp hn).1
    exact h0 (by simp [this])
  have e : run (correctionZ h as bs ss dst carry q cin) m s=run (correction h as bs ss dst carry q cin) m s := by
    simp only [correctionZ,correction,run_append]
    exact incr1_run _ _ _ _ _ ui hc
  rw [e]
  exact correction_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s m hv hq0 hi0 hc0

theorem correctionBackZ_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)-
      (2^(2*h-1) : Nat)) s (run (correctionBackZ h as bs ss dst carry q cin) m s) := by
  have hc : ∀c∈(carry.take 2).take 1,cin≠c := by
    intro c hc e; subst e
    have := List.mem_of_mem_take (List.mem_of_mem_take hc)
    have h0 := (List.nodup_cons.mp hn).1
    exact h0 (by simp [this])
  have hy : cin∉dst.drop (2*h-1) := by
    intro hy
    have h0 := (List.nodup_cons.mp hn).1
    exact h0 (by simp [List.mem_of_mem_drop hy])
  have hyn : (dst.drop (2*h-1)).Nodup := by
    apply List.Nodup.sublist (List.drop_sublist _ _)
    exact nd_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega)
  have e : run (correctionBackZ h as bs ss dst carry q cin) m s=run (correctionBack h as bs ss dst carry q cin) m s := by
    simp only [correctionBackZ,correctionBack,run_append]
    have mc : measurementCount (decr1 (dst.drop (2*h-1)) (carry.take 2) cin)=
        measurementCount (mappedSub (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin) := by
      have a := incr1_counts (dst.drop (2*h-1)) (carry.take 2) cin
        (by simp only [List.length_drop]; rcases hh with rfl|rfl <;> omega)
        (by simp only [List.length_take]; omega)
      simp only [decr1,mappedSub,measurementCount_append,a.2]
    rw [mc,decr1_run _ _ _ _ _ hi0 hc hy hyn]
  rw [e]
  exact correctionBack_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s m hv hq0 hi0 hc0

def corrZ (R : KRegs) : Program := correctionZ R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
def corrBackZ (R : KRegs) : Program := correctionBackZ R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin

theorem corrZ_mem (R : KRegs) : ∀i∈corrZ R,i∈corr R := by
  intro i h
  simp only [corrZ,corr,correctionZ,correction,List.mem_append] at h ⊢
  rcases h with h|h
  · exact Or.inl h
  · exact Or.inr (incr1_mem _ _ _ i h)
theorem corrBackZ_mem (R : KRegs) : ∀i∈corrBackZ R,i∈corrBack R := by
  intro i h
  simp only [corrBackZ,corrBack,correctionBackZ,correctionBack,decr1,mappedSub,List.mem_append] at h ⊢
  rcases h with ((h|h)|h)|h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr (incr1_mem _ _ _ i h)))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem corrZ_counts (R : KRegs) (w : R.W) :
    toffoliCount (corrZ R)+1=toffoliCount (corr R) ∧ measurementCount (corrZ R)=measurementCount (corr R) := by
  have hTl := w.T; have hSl := w.S; have hcl := w.carry; have hh2 := w.hh; have h5 := w.h5
  have a := incr1_counts (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
    (by simp only [List.length_drop]; have h4 := w.h4; omega)
    (by simp only [List.length_take]; omega)
  simp only [corrZ,corr,correctionZ,correction,toffoliCount_append,measurementCount_append]
  omega
theorem corrBackZ_counts (R : KRegs) (w : R.W) :
    toffoliCount (corrBackZ R)+1=toffoliCount (corrBack R) ∧ measurementCount (corrBackZ R)=measurementCount (corrBack R) := by
  have hTl := w.T; have hSl := w.S; have hcl := w.carry; have hh2 := w.hh; have h5 := w.h5
  have a := incr1_counts (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
    (by simp only [List.length_drop]; have h4 := w.h4; omega)
    (by simp only [List.length_take]; omega)
  simp only [corrBackZ,corrBack,correctionBackZ,correctionBack,decr1,mappedSub,toffoliCount_append,measurementCount_append]
  omega
theorem corrZ_slots (R : KRegs) : Challenge.gateSlots (corrZ R)≤Challenge.gateSlots (corr R) := by
  have a := incr1_slots (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
  simp only [corrZ,corr,correctionZ,correction,Challenge.gateSlots_append]
  omega
theorem corrBackZ_slots (R : KRegs) : Challenge.gateSlots (corrBackZ R)≤Challenge.gateSlots (corrBack R) := by
  have a := incr1_slots (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
  simp only [corrBackZ,corrBack,correctionBackZ,correctionBack,decr1,mappedSub,Challenge.gateSlots_append]
  omega

theorem corrZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (base : State) (hz0 : regValue R.z base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) (T-((2^R.h : Nat) : Int)*(sharedWord R.h (regValue R.lo base.basis) (regValue R.hi base.basis)+1)+(2^(2*R.h-1) : Nat))) (corrZ R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hzl := w.z
  have hhi : R.hi.length=R.h := by omega
  have hs : R.S.length=R.h+1 := by omega
  have qm : parity R∈R.z := getD_in R.z 0 (by omega)
  have qsub : List.Sublist [parity R] R.z := List.singleton_sublist.mpr qm
  have cn : (R.cin::parity R::R.lo++R.hi++R.S++R.T++R.carry).Nodup := knd hn (fun q => by
    have c := R.counts q; have z := qsub.count_le q
    simp only [KRegs.all,List.count_cons,List.count_append,List.count_nil] at c z ⊢; omega)
  have av := regValue_lt R.lo base.basis
  have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hhi] at bv
  have slt : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [hs,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) slt
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have zv := (ht.keep hn R.z (by intro q h; simp [h])).trans hz0
  have r := correctionZ_correct R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
    hh L0 hhi hs (by omega) (by omega) cn t rec (by rw [sv,al,bl])
    ((regValue_zero _ _).mp zv _ qm) ((ht.cin hn).trans hi0) cv
  rw [al,bl] at r
  have act := ht.advance hn 3 _ r
  convert act using 1 <;> simp only [vec3]
  congr 1
  change _=T+_
  ring

theorem corrBackZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (base : State) (hz0 : regValue R.z base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) (T+((2^R.h : Nat) : Int)*(sharedWord R.h (regValue R.lo base.basis) (regValue R.hi base.basis)+1)-(2^(2*R.h-1) : Nat))) (corrBackZ R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hzl := w.z
  have hhi : R.hi.length=R.h := by omega
  have hs : R.S.length=R.h+1 := by omega
  have qm : parity R∈R.z := getD_in R.z 0 (by omega)
  have qsub : List.Sublist [parity R] R.z := List.singleton_sublist.mpr qm
  have cn : (R.cin::parity R::R.lo++R.hi++R.S++R.T++R.carry).Nodup := knd hn (fun q => by
    have c := R.counts q; have z := qsub.count_le q
    simp only [KRegs.all,List.count_cons,List.count_append,List.count_nil] at c z ⊢; omega)
  have av := regValue_lt R.lo base.basis
  have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hhi] at bv
  have slt : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [hs,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) slt
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have zv := (ht.keep hn R.z (by intro q h; simp [h])).trans hz0
  have r := correctionBackZ_correct R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
    hh L0 hhi hs (by omega) (by omega) cn t rec (by rw [sv,al,bl])
    ((regValue_zero _ _).mp zv _ qm) ((ht.cin hn).trans hi0) cv
  rw [al,bl] at r
  have act := ht.advance hn 3 _ r
  convert act using 1 <;> simp only [vec3]
  congr 1
  change _=T+_
  ring


end ECDSAAdd.Entrant.DiagSq
end

section
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-! Diagonal add/subtract whose lowest target bit is known. The bit-0 majority of
`mappedAdd (mappedDiagonal xs)` is `majority x₀ y₀ cin c`; with `cin = 0` its Toffoli
fires on `(y₀ ⊕ x₀) ∧ x₀`, which is zero whenever `x₀ → y₀`. For the subtraction
(complemented target) this holds when the target is even, for the addition when the
target's bit 0 equals `x₀`. `addHead0` drops that Toffoli (its carry is then just `x₀`). -/

theorem ccx_noop2 (a b t : Wire) (p : Program) (m : List Bool) (s : State)
    (h : (s.basis a && s.basis b)=false) : run (.CCX a b t :: p) m s=run p m s := by
  have e : (⟨s.phase,writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))⟩ : State)=s := by
    obtain ⟨ph,bs⟩ := s
    simp only at h
    congr 1
    funext q
    by_cases hq : q=t
    · subst hq; simp [writeBit,h]
    · simp [writeBit,Function.update,hq]
  simp only [run]
  rw [e]

theorem run_maj_idle (a y cin c : Wire) (X : Program) (m : List Bool) (s : State)
    (hi : s.basis cin=false) (hay : s.basis a=true → s.basis y=true)
    (h1 : a≠y) (h3 : y≠cin) :
    run (.CX a y :: .CX a cin :: .CCX y cin c :: X) m s=run (.CX a y :: .CX a cin :: X) m s := by
  let t1 : State := ⟨s.phase,writeBit s.basis y (s.basis y ^^ s.basis a)⟩
  let t2 : State := ⟨t1.phase,writeBit t1.basis cin (t1.basis cin ^^ t1.basis a)⟩
  have ht2 : (t2.basis y && t2.basis cin)=false := by
    have e1 : t2.basis y=(s.basis y ^^ s.basis a) := by
      simp [t2,t1,writeBit,Function.update,h3]
    have e2 : t2.basis cin=s.basis a := by
      simp [t2,t1,writeBit,Function.update,h3.symm,h1,hi]
    rw [e1,e2]
    cases ha : s.basis a <;> cases hy : s.basis y <;> simp_all
  calc run (.CX a y :: .CX a cin :: .CCX y cin c :: X) m s=run (.CCX y cin c :: X) m t2 := rfl
    _=run X m t2 := ccx_noop2 _ _ _ _ _ _ ht2
    _=run (.CX a y :: .CX a cin :: X) m s := rfl

def maj0 (a y cin c : Wire) : Program := [.CX a y,.CX a cin,.CX a c,.CX a cin,.CX a y]

def addHead0 (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) : Program :=
  match bits, ys, carry with
  | ⟨some a,false⟩::b'::bits', y::y'::ys', c::cs =>
      maj0 a y cin c++(mappedAdd (b'::bits') (y'::ys') cs c++
        mappedEraseCarry ⟨some a,false⟩ y cin c++mappedSum ⟨some a,false⟩ y cin)
  | bits, ys, carry => mappedAdd bits ys carry cin

theorem addHead0_split (a y y' c cin : Wire) (b' : MappedBit) (bits : List MappedBit) (ys cs : List Wire) :
    mappedAdd (⟨some a,false⟩::b'::bits) (y::y'::ys) (c::cs) cin=
      majority a y cin c++(mappedAdd (b'::bits) (y'::ys) cs c++
        mappedEraseCarry ⟨some a,false⟩ y cin c++mappedSum ⟨some a,false⟩ y cin) := by
  simp [mappedAdd,mappedMajority,List.append_assoc]

theorem addHead0_run (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (m : List Bool) (s : State)
    (hi : s.basis cin=false) (hay : ∀y ys',ys=y::ys' → s.basis a=true → s.basis y=true)
    (h1 : a∉ys) (h3 : cin∉ys) :
    run (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin) m s=
      run (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) m s := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try rfl
  rw [addHead0_split]
  simp only [addHead0,maj0,majority,List.cons_append,List.nil_append]
  exact (run_maj_idle a y cin c _ m s hi (hay y _ rfl) (fun e => h1 (by simp [e]))
    (fun e => h3 (by simp [e]))).symm

theorem addHead0_mem (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    ∀i∈addHead0 (⟨some a,false⟩::b'::bits) ys carry cin,i∈mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try (intro i h; exact h)
  rw [addHead0_split]
  intro i h
  simp only [addHead0,maj0,majority,List.mem_append,List.mem_cons] at h ⊢
  tauto

theorem addHead0_mc (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    measurementCount (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin)=
      measurementCount (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> rfl

theorem addHead0_counts (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (h2 : 2≤ys.length) (hc : 1≤carry.length) :
    toffoliCount (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin)+1=
      toffoliCount (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) ∧
    measurementCount (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin)=
      measurementCount (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> simp at h2 hc
  rw [addHead0_split]
  simp only [addHead0,maj0,majority,toffoliCount_append,measurementCount_append]
  simp [toffoliCount,measurementCount]
  omega

theorem addHead0_slots (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin)≤
      Challenge.gateSlots (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try exact le_refl _
  rw [addHead0_split]
  simp only [addHead0,maj0,majority,Challenge.gateSlots_append]
  simp [Challenge.gateSlots,Challenge.instructionSlots]

theorem diag_cons (x : Wire) (xs : List Wire) :
    ∃ b' bits,mappedDiagonal (x::xs)=⟨some x,false⟩::b'::bits := by
  cases xs with
  | nil => exact ⟨_,_,rfl⟩
  | cons x' xs => exact ⟨_,_,rfl⟩

def dAddZ (xs dst carry : List Wire) (cin : Wire) : Program :=
  addHead0 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin

def dSubZ (xs dst carry : List Wire) (cin : Wire) : Program :=
  notRegister dst++dAddZ xs dst carry cin++notRegister dst

theorem dAddZ_mem (xs dst carry : List Wire) (cin : Wire) :
    ∀i∈dAddZ xs dst carry cin,i∈mappedDiagAdd xs dst carry cin := by
  rcases xs with _|⟨x,xs⟩
  · intro i h; exact h
  · obtain ⟨b',bits,e⟩ := diag_cons x xs
    simp only [dAddZ,mappedDiagAdd,e]
    exact addHead0_mem _ _ _ _ _ _

theorem dSubZ_mem (xs dst carry : List Wire) (cin : Wire) :
    ∀i∈dSubZ xs dst carry cin,i∈mappedDiagSub xs dst carry cin := by
  intro i h
  simp only [dSubZ,mappedDiagSub,mappedSub,List.mem_append] at h ⊢
  rcases h with (h|h)|h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (dAddZ_mem xs dst carry cin i h))
  · exact Or.inr h

theorem dAddZ_counts (xs dst carry : List Wire) (cin : Wire) (hx : 0<xs.length)
    (hd : 2≤dst.length) (hc : 1≤carry.length) :
    toffoliCount (dAddZ xs dst carry cin)+1=toffoliCount (mappedDiagAdd xs dst carry cin) ∧
    measurementCount (dAddZ xs dst carry cin)=measurementCount (mappedDiagAdd xs dst carry cin) := by
  rcases xs with _|⟨x,xs⟩
  · simp at hx
  · obtain ⟨b',bits,e⟩ := diag_cons x xs
    simp only [dAddZ,mappedDiagAdd,e]
    exact addHead0_counts _ _ _ _ _ _ hd (by simp only [List.length_take]; omega)

theorem dSubZ_counts (xs dst carry : List Wire) (cin : Wire) (hx : 0<xs.length)
    (hd : 2≤dst.length) (hc : 1≤carry.length) :
    toffoliCount (dSubZ xs dst carry cin)+1=toffoliCount (mappedDiagSub xs dst carry cin) ∧
    measurementCount (dSubZ xs dst carry cin)=measurementCount (mappedDiagSub xs dst carry cin) := by
  have a := dAddZ_counts xs dst carry cin hx hd hc
  simp only [dAddZ,mappedDiagAdd] at a
  simp only [dSubZ,dAddZ,mappedDiagSub,mappedSub,toffoliCount_append,measurementCount_append]
  omega

theorem dAddZ_slots (xs dst carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (dAddZ xs dst carry cin)≤Challenge.gateSlots (mappedDiagAdd xs dst carry cin) := by
  rcases xs with _|⟨x,xs⟩
  · exact le_refl _
  · obtain ⟨b',bits,e⟩ := diag_cons x xs
    simp only [dAddZ,mappedDiagAdd,e]
    exact addHead0_slots _ _ _ _ _ _

theorem dSubZ_slots (xs dst carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (dSubZ xs dst carry cin)≤Challenge.gateSlots (mappedDiagSub xs dst carry cin) := by
  have a := dAddZ_slots xs dst carry cin
  simp only [dAddZ,mappedDiagAdd] at a
  simp only [dSubZ,dAddZ,mappedDiagSub,mappedSub,Challenge.gateSlots_append]
  omega

theorem dAddZ_run (xs dst carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin::xs++dst++carry).Nodup) (hi : s.basis cin=false)
    (hay : ∀y ys',dst=y::ys' → s.basis (xs.headD 0)=true → s.basis y=true) :
    run (dAddZ xs dst carry cin) m s=run (mappedDiagAdd xs dst carry cin) m s := by
  rcases xs with _|⟨x,xs⟩
  · rfl
  · obtain ⟨b',bits,e⟩ := diag_cons x xs
    simp only [dAddZ,mappedDiagAdd,e]
    have hx : x∉dst := dis_count (r:=x::xs) (t:=dst) hn (fun w => by simp only [List.count_cons,List.count_append]; omega) x (by simp)
    have hc : cin∉dst := dis_count (r:=[cin]) (t:=dst) hn (fun w => by simp only [List.count_cons,List.count_append,List.count_nil]; omega) cin (by simp)
    exact addHead0_run x b' bits dst _ cin m s hi (by simpa using hay) hx hc

theorem dSubZ_run (xs dst carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin::xs++dst++carry).Nodup) (hi : s.basis cin=false)
    (hy : s.basis (dst.headD 0)=false) :
    run (dSubZ xs dst carry cin) m s=run (mappedDiagSub xs dst carry cin) m s := by
  have hm : measurementCount (notRegister dst)=0 := (notRegister_counts dst).2
  have hdn : dst.Nodup := nd_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega)
  have nr := notRegister_correct dst hdn s []
  have hc : cin∉dst := dis_count (r:=[cin]) (t:=dst) hn (fun w => by simp only [List.count_cons,List.count_append,List.count_nil]; omega) cin (by simp)
  have mc : measurementCount (dAddZ xs dst carry cin)=measurementCount (mappedAdd (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin) := by
    rcases xs with _|⟨x,xs⟩
    · rfl
    · obtain ⟨b',bits,e⟩ := diag_cons x xs
      simp only [dAddZ,e]
      exact addHead0_mc _ _ _ _ _ _
  simp only [dSubZ,mappedDiagSub,mappedSub,List.append_assoc]
  rw [run_append (notRegister dst),run_append (notRegister dst),hm]
  simp only [List.take_zero,List.drop_zero]
  rw [run_append (dAddZ xs dst carry cin),run_append (mappedAdd (mappedDiagonal xs) dst _ cin),mc]
  have e := dAddZ_run xs dst carry cin (m.take (measurementCount (mappedAdd (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin)))
    (run (notRegister dst) [] s) hn (by rw [nr]; simp [hc,hi]) (by
      intro y ys' e _
      subst e
      rw [nr]
      simp at hy ⊢; simp [hy])
  simp only [dAddZ,mappedDiagAdd] at e
  simp only [dAddZ]
  rw [e]

end ECDSAAdd.Entrant.DiagSq
end

section
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic

/-! Bit 1 of a square is always zero (`b² mod 4 ∈ {0,1}`). In `m7g : T −= b²` and
`c7g : T += b²` the bit-0 carry is already dropped (its carry-in for bit 1 is the clean
`cin`), so the bit-1 majority has source bit `0` and carry-in `0`: its Toffoli is idle.
`addHeadI` drops the Toffoli of the first majority of an in-place adder whose first
source bit is zero. -/

def addHeadI : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as, b::b'::bs, c::cs, cin =>
      DiagSq.maj0 a b cin c++(addInPlace (a'::as) (b'::bs) cs c++eraseCarry a b cin c++[.CX a b,.CX cin b])
  | x, y, c, cin => addInPlace x y c cin

theorem addHeadI_split (a a' b b' c cin : Wire) (as bs cs : List Wire) :
    addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin=
      majority a b cin c++(addInPlace (a'::as) (b'::bs) cs c++eraseCarry a b cin c++[.CX a b,.CX cin b]) := by
  simp [addInPlace,List.append_assoc]

theorem addHeadI_run (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hi : s.basis cin=false) (h0 : ∀a as,x=a::as → s.basis a=false)
    (hd : ∀a as b bs,x=a::as → y=b::bs → a≠b ∧ a≠cin ∧ b≠cin) :
    run (addHeadI x y carry cin) m s=run (addInPlace x y carry cin) m s := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try rfl
  rw [addHeadI_split]
  obtain ⟨h1,-,h3⟩ := hd a _ b _ rfl rfl
  simp only [addHeadI,DiagSq.maj0,majority,List.cons_append,List.nil_append]
  exact (DiagSq.run_maj_idle a b cin c _ m s hi (by intro h; rw [h0 a _ rfl] at h; cases h) h1 h3).symm

theorem addHeadI_mem (x y carry : List Wire) (cin : Wire) :
    ∀i∈addHeadI x y carry cin,i∈addInPlace x y carry cin := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;>
    try (intro i h; exact h)
  rw [addHeadI_split]
  intro i h
  simp only [addHeadI,DiagSq.maj0,majority,List.mem_append,List.mem_cons] at h ⊢
  tauto

theorem addHeadI_counts (x y carry : List Wire) (cin : Wire) (hx : 2≤x.length) (hy : 2≤y.length)
    (hc : 1≤carry.length) :
    toffoliCount (addHeadI x y carry cin)+1=toffoliCount (addInPlace x y carry cin) ∧
    measurementCount (addHeadI x y carry cin)=measurementCount (addInPlace x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;>
    simp at hx hy hc
  rw [addHeadI_split]
  simp only [addHeadI,DiagSq.maj0,majority,toffoliCount_append,measurementCount_append]
  simp [toffoliCount,measurementCount]
  omega

theorem addHeadI_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addHeadI x y carry cin)≤Challenge.gateSlots (addInPlace x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;>
    try exact le_refl _
  rw [addHeadI_split]
  simp only [addHeadI,DiagSq.maj0,majority,Challenge.gateSlots_append]
  simp [Challenge.gateSlots,Challenge.instructionSlots]

theorem addHeadI_mc (x y carry : List Wire) (cin : Wire) :
    measurementCount (addHeadI x y carry cin)=measurementCount (addInPlace x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> rfl

/-- `addLowNC` with the bit-1 Toffoli also dropped. -/
def addLowNC1 (x y carry : List Wire) (cin : Wire) : Program :=
  addHeadI x.tail y.tail carry.tail cin ++ [.measureX (carry.headD 0) [] []] ++
    [.CX (x.headD 0) (y.headD 0), .CX cin (y.headD 0)]

def subLowNC1 (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addLowNC1 x y carry cin ++ notRegister y

theorem addLowNC1_mc (x y carry : List Wire) (cin : Wire) :
    measurementCount (addLowNC1 x y carry cin)=measurementCount (LowZero.addLowNC x y carry cin) := by
  simp only [addLowNC1,LowZero.addLowNC,measurementCount_append,addHeadI_mc]

theorem addLowNC1_run (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hi : s.basis cin=false)
    (h1 : s.basis (x.tail.headD 0)=false) :
    run (addLowNC1 x y carry cin) m s=run (LowZero.addLowNC x y carry cin) m s := by
  have hd : ∀a as b bs,x.tail=a::as → y.tail=b::bs → a≠b ∧ a≠cin ∧ b≠cin := by
    intro a as b bs ha hb
    have ax : a∈x := List.mem_of_mem_tail (by rw [ha]; simp)
    have bx : b∈y := List.mem_of_mem_tail (by rw [hb]; simp)
    have hc := (List.nodup_cons.mp hn).1
    refine ⟨fun e => ?_,fun e => hc (by rw [← e]; simp [ax]),fun e => hc (by rw [← e]; simp [bx])⟩
    rw [e] at ax
    exact DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) b ax bx
  have h0 : ∀a as,x.tail=a::as → s.basis a=false := by
    intro a as h; have := h1; rw [h] at this; simpa using this
  have e := addHeadI_run x.tail y.tail carry.tail cin
    (m.take (measurementCount (addInPlace x.tail y.tail carry.tail cin))) s hi h0 hd
  simp only [addLowNC1,LowZero.addLowNC,List.append_assoc]
  rw [run_append (addHeadI _ _ _ _),run_append (addInPlace _ _ _ _),addHeadI_mc,e]

theorem subLowNC1_run (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hi : s.basis cin=false)
    (h1 : s.basis (x.tail.headD 0)=false) (hx : 2≤x.length) :
    run (subLowNC1 x y carry cin) m s=run (LowZero.subLowNC x y carry cin) m s := by
  have hm : measurementCount (notRegister y)=0 := (notRegister_counts y).2
  have hyn : y.Nodup := DiagSq.nd_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega)
  have nr := notRegister_correct y hyn s []
  have hc : cin∉y := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hx1 : x.tail.headD 0∈x := by rcases x with _|⟨a,_|⟨b,xs⟩⟩ <;> simp at hx ⊢
  have hx2 : x.tail.headD 0∉y :=
    DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) _ hx1
  simp only [subLowNC1,LowZero.subLowNC,List.append_assoc]
  rw [run_append (notRegister y),run_append (notRegister y),hm]
  simp only [List.take_zero,List.drop_zero]
  rw [run_append (addLowNC1 x y carry cin),
    run_append (LowZero.addLowNC x y carry cin),addLowNC1_mc,
    addLowNC1_run x y carry cin _ _ hn (by rw [nr]; simp [hc,hi]) (by rw [nr]; dsimp only; rw [if_neg hx2]; exact h1)]

theorem addLowNC1_mem (x y carry : List Wire) (cin : Wire) :
    ∀i∈addLowNC1 x y carry cin,i∈LowZero.addLowNC x y carry cin := by
  intro i h
  simp only [addLowNC1,LowZero.addLowNC,List.mem_append] at h ⊢
  rcases h with (h|h)|h
  · exact Or.inl (Or.inl (addHeadI_mem _ _ _ _ i h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem subLowNC1_mem (x y carry : List Wire) (cin : Wire) :
    ∀i∈subLowNC1 x y carry cin,i∈LowZero.subLowNC x y carry cin := by
  intro i h
  simp only [subLowNC1,LowZero.subLowNC,List.mem_append] at h ⊢
  rcases h with (h|h)|h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (addLowNC1_mem _ _ _ _ i h))
  · exact Or.inr h

theorem addLowNC1_counts (x y carry : List Wire) (cin : Wire) (hx : 3≤x.length) (hy : 3≤y.length)
    (hc : 2≤carry.length) :
    toffoliCount (addLowNC1 x y carry cin)+1=toffoliCount (LowZero.addLowNC x y carry cin) := by
  have a := addHeadI_counts x.tail y.tail carry.tail cin (by simp; omega) (by simp; omega) (by simp; omega)
  simp only [addLowNC1,LowZero.addLowNC,toffoliCount_append]
  omega

theorem subLowNC1_counts (x y carry : List Wire) (cin : Wire) (hx : 3≤x.length) (hy : 3≤y.length)
    (hc : 2≤carry.length) :
    toffoliCount (subLowNC1 x y carry cin)+1=toffoliCount (LowZero.subLowNC x y carry cin) := by
  have a := addLowNC1_counts x y carry cin hx hy hc
  simp only [subLowNC1,LowZero.subLowNC,toffoliCount_append]
  omega

theorem addLowNC1_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addLowNC1 x y carry cin)≤Challenge.gateSlots (LowZero.addLowNC x y carry cin) := by
  have a := addHeadI_slots x.tail y.tail carry.tail cin
  simp only [addLowNC1,LowZero.addLowNC,Challenge.gateSlots_append]
  omega

theorem subLowNC1_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (subLowNC1 x y carry cin)≤Challenge.gateSlots (LowZero.subLowNC x y carry cin) := by
  have a := addLowNC1_slots x y carry cin
  simp only [subLowNC1,LowZero.subLowNC,Challenge.gateSlots_append]
  omega

theorem bit1 (r tail : List Wire) (st : BasisState) (hl : 2≤r.length) :
    st ((r++tail).tail.headD 0)=decide (regValue r st/2%2=1) := by
  match r, hl with
  | w::ws, hl2 =>
    have hne : ws≠[] := by intro e; subst e; simp at hl2
    simp only [List.cons_append,List.tail_cons]
    rw [LowZero.head_bit ws tail st hne,LowZero.foldr_cons_value]
    have : ((if st w then 1 else 0)+2*regValue ws st)/2=regValue ws st := by split <;> omega
    rw [this]

theorem sq_bit1 (b : Nat) : b^2/2%2=0 := by
  have h : b^2%4=0 ∨ b^2%4=1 := by
    rw [Nat.pow_mod]
    have : b%4<4 := Nat.mod_lt _ (by norm_num)
    interval_cases (b%4) <;> simp
  omega

variable (R : KRegs)

theorem dhi_two (w : R.W) : 2≤R.dhi.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  omega

def m7y : Program :=
  if (R.dhi++R.zB).length=R.T.length ∧ (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length then
    subLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin else R.m7g
def c7y : Program :=
  if (R.dhi++R.zB).length=R.T.length ∧ (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length then
    addLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin else R.c7g

theorem m7y_mem : ∀i∈R.m7y,i∈R.m7g := by
  unfold m7y
  split_ifs with h
  · unfold m7g; rw [LowZero.subLowNCG_eq _ _ _ _ h.1 h.2.1 h.2.2]; exact subLowNC1_mem _ _ _ _
  · exact fun i hi => hi
theorem c7y_mem : ∀i∈R.c7y,i∈R.c7g := by
  unfold c7y
  split_ifs with h
  · unfold c7g; rw [LowZero.addLowNCG_eq _ _ _ _ h.1 h.2.1 h.2.2]; exact addLowNC1_mem _ _ _ _
  · exact fun i hi => hi

theorem m7y_wires : wires R.m7y⊆wires R.m7 := (DiagSq.wires_of_mem R.m7y_mem).trans R.m7g_wires
theorem c7y_wires : wires R.c7y⊆wires R.c7 := (DiagSq.wires_of_mem R.c7y_mem).trans R.c7g_wires
theorem m7y_physical (hn : R.all.Nodup) : GatePhysical R.m7y := fun i hi => R.m7g_physical hn i (R.m7y_mem i hi)
theorem c7y_physical (hn : R.all.Nodup) : GatePhysical R.c7y := fun i hi => R.c7g_physical hn i (R.c7y_mem i hi)

theorem m7y_slots : Challenge.gateSlots R.m7y≤Challenge.gateSlots R.m7 := by
  refine le_trans ?_ R.m7g_slots
  unfold m7y
  split_ifs with h
  · unfold m7g; rw [LowZero.subLowNCG_eq _ _ _ _ h.1 h.2.1 h.2.2]; exact subLowNC1_slots _ _ _ _
  · exact le_refl _
theorem c7y_slots : Challenge.gateSlots R.c7y≤Challenge.gateSlots R.c7 := by
  refine le_trans ?_ R.c7g_slots
  unfold c7y
  split_ifs with h
  · unfold c7g; rw [LowZero.addLowNCG_eq _ _ _ _ h.1 h.2.1 h.2.2]; exact addLowNC1_slots _ _ _ _
  · exact le_refl _

theorem m7y_counts (w : R.W) : toffoliCount R.m7y+2=toffoliCount R.m7 ∧
    measurementCount R.m7y=measurementCount R.m7 := by
  have l := R.t_lensg w
  have z := R.m7g_counts w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have c := subLowNC1_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by rw [l.1]; omega) (by omega) (by simp only [List.length_take]; omega)
  have mc : measurementCount R.m7y=measurementCount R.m7g := by
    unfold m7y m7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
    simp only [subLowNC1,LowZero.subLowNC,measurementCount_append,addLowNC1_mc]
  have tc : toffoliCount R.m7y+1=toffoliCount R.m7g := by
    unfold m7y m7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]; exact c
  constructor <;> omega
theorem c7y_counts (w : R.W) : toffoliCount R.c7y+2=toffoliCount R.c7 ∧
    measurementCount R.c7y=measurementCount R.c7 := by
  have l := R.t_lensg w
  have z := R.c7g_counts w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have c := addLowNC1_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by rw [l.1]; omega) (by omega) (by simp only [List.length_take]; omega)
  have mc : measurementCount R.c7y=measurementCount R.c7g := by
    unfold c7y c7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
    exact addLowNC1_mc _ _ _ _
  have tc : toffoliCount R.c7y+1=toffoliCount R.c7g := by
    unfold c7y c7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]; exact c
  constructor <;> omega

theorem m7y_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false) :
    (run R.m7y m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m7y m s).basis q=s.basis q) ∧
    regValue R.T (run R.m7y m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dhi++R.zB) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lensg w
  have e : run R.m7y m s=run R.m7g m s := by
    unfold m7y m7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
    exact subLowNC1_run _ _ _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) hi h1 (by rw [l.1]; exact l.2.2.1)
  rw [e]; exact R.m7g_correct w hn s m hcl hnc hi
theorem c7y_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false) :
    (run R.c7y m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c7y m s).basis q=s.basis q) ∧
    regValue R.T (run R.c7y m s).basis=(regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lensg w
  have e : run R.c7y m s=run R.c7g m s := by
    unfold c7y c7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
    exact addLowNC1_run _ _ _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) hi h1
  rw [e]; exact R.c7g_correct w hn s m hcl hnc hi

end ECDSAAdd.Entrant.KRegs
end

section
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic

/-! Inner `T −= A` / `T += A` with a bounded low part. In every inner leaf the subtracted
value `A = rawValue h a < 2^{2h}` never exceeds the low `2h+1` bits of `T = rawValue (h+1) S`,
so the borrow out of bit `2h` is always zero and the 66/68-bit adder can run on the low
`2h+1` bits only (one majority/erase pair fewer). -/

theorem add_take_sublist (n : Nat) : ∀ (x y c : List Wire) (cin : Wire), x.length=n+2 → y.length=n+2 →
    c.length=n+1 →
    (addInPlace (x.take (n+1)) (y.take (n+1)) (c.take n) cin).Sublist (addInPlace x y c cin) := by
  induction n with
  | zero =>
    intro x y c cin hx hy hc
    match x, y, c, hx, hy, hc with
    | [a,a'], [b,b'], [c0], _, _, _ =>
      simp only [List.take, addInPlace]
      exact List.sublist_append_right _ _
  | succ n ih =>
    intro x y c cin hx hy hc
    match x, y, c, hx, hy, hc with
    | a::a'::x', b::b'::y', c0::c', hx, hy, hc =>
      have hx' : (a'::x').length=n+2 := by simpa using hx
      have hy' : (b'::y').length=n+2 := by simpa using hy
      have hc' : c'.length=n+1 := by simpa using hc
      have r := ih (a'::x') (b'::y') c' c0 hx' hy' hc'
      simp only [List.take_succ_cons] at r ⊢
      simp only [addInPlace]
      exact ((((List.Sublist.refl _).append r).append (List.Sublist.refl _)).append (List.Sublist.refl _))

theorem slots_sublist {p q : Program} (h : p.Sublist q) : Challenge.gateSlots p≤Challenge.gateSlots q := by
  unfold Challenge.gateSlots
  exact (h.map _).sum_le_sum (fun _ _ => Nat.zero_le _)

theorem notRegister_take_sublist (y : List Wire) (k : Nat) : (notRegister (y.take k)).Sublist (notRegister y) := by
  unfold notRegister
  rw [List.map_take]
  exact List.take_sublist _ _

/-- `addLowNC` on the low `k+2` bits is a sublist of `addLowNC` on all bits. -/
theorem addLowNC_take_sublist (n : Nat) (x y c : List Wire) (cin : Wire) (hx : x.length=n+3) (hy : y.length=n+3)
    (hc : c.length=n+2) :
    (LowZero.addLowNC (x.take (n+2)) (y.take (n+2)) (c.take (n+1)) cin).Sublist (LowZero.addLowNC x y c cin) := by
  match x, y, c, hx, hy, hc with
  | a::x', b::y', c0::c', hx, hy, hc =>
    have r := add_take_sublist n x' y' c' cin (by simpa using hx) (by simpa using hy) (by simpa using hc)
    simp only [LowZero.addLowNC,List.take_succ_cons,List.tail_cons,List.headD_cons]
    exact (r.append (List.Sublist.refl _)).append (List.Sublist.refl _)

theorem subLowNC_take_sublist (n : Nat) (x y c : List Wire) (cin : Wire) (hx : x.length=n+3) (hy : y.length=n+3)
    (hc : c.length=n+2) :
    (LowZero.subLowNC (x.take (n+2)) (y.take (n+2)) (c.take (n+1)) cin).Sublist (LowZero.subLowNC x y c cin) := by
  simp only [LowZero.subLowNC]
  exact ((notRegister_take_sublist y (n+2)).append (addLowNC_take_sublist n x y c cin hx hy hc)).append
    (notRegister_take_sublist y (n+2))

variable (R : KRegs)

def lowOK : Prop := (R.dlo++R.zA).length=R.T.length ∧ (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 3≤R.T.length

instance : Decidable R.lowOK := by unfold lowOK; infer_instance

def m6w : Program := if R.lowOK then
  LowZero.subLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin else R.m6z
def c6w : Program := if R.lowOK then
  LowZero.addLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin else R.c6z

theorem lowOK_of (w : R.W) : R.lowOK := by
  have l := R.lo_lens w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  exact ⟨l.1,l.2.1,by omega⟩

theorem m6w_sub : R.m6w.Sublist R.m6z := by
  unfold m6w
  split_ifs with h
  · obtain ⟨h1,h2,h3⟩ := h
    unfold m6z; rw [LowZero.subLowNCG_eq _ _ _ _ h1 h2 (by omega)]
    have e1 : R.T.length-1=(R.T.length-3)+2 := by omega
    have e2 : R.T.length-2=(R.T.length-3)+1 := by omega
    rw [e1,e2]
    exact subLowNC_take_sublist _ _ _ _ _ (by omega) (by omega)
      (by rw [List.length_take]; simp only [List.length_take] at h2; omega)
  · exact List.Sublist.refl _
theorem c6w_sub : R.c6w.Sublist R.c6z := by
  unfold c6w
  split_ifs with h
  · obtain ⟨h1,h2,h3⟩ := h
    unfold c6z; rw [LowZero.addLowNCG_eq _ _ _ _ h1 h2 (by omega)]
    have e1 : R.T.length-1=(R.T.length-3)+2 := by omega
    have e2 : R.T.length-2=(R.T.length-3)+1 := by omega
    rw [e1,e2]
    exact addLowNC_take_sublist _ _ _ _ _ (by omega) (by omega)
      (by rw [List.length_take]; simp only [List.length_take] at h2; omega)
  · exact List.Sublist.refl _

theorem m6w_wires : wires R.m6w⊆wires R.m6 :=
  (DiagSq.wires_of_mem (fun _ h => (R.m6w_sub).subset h)).trans R.m6z_wires
theorem c6w_wires : wires R.c6w⊆wires R.c6 :=
  (DiagSq.wires_of_mem (fun _ h => (R.c6w_sub).subset h)).trans R.c6z_wires
theorem m6w_slots : Challenge.gateSlots R.m6w≤Challenge.gateSlots R.m6 :=
  (slots_sublist R.m6w_sub).trans R.m6z_slots
theorem c6w_slots : Challenge.gateSlots R.c6w≤Challenge.gateSlots R.c6 :=
  (slots_sublist R.c6w_sub).trans R.c6z_slots
theorem m6w_physical (hn : R.all.Nodup) : GatePhysical R.m6w :=
  fun i h => R.m6z_physical hn i ((R.m6w_sub).subset h)
theorem c6w_physical (hn : R.all.Nodup) : GatePhysical R.c6w :=
  fun i h => R.c6z_physical hn i ((R.c6w_sub).subset h)

theorem m6w_counts (w : R.W) : toffoliCount R.m6w+2=toffoliCount R.m6 ∧
    measurementCount R.m6w+1=measurementCount R.m6 := by
  have z := R.m6z_counts w
  obtain ⟨h1,h2,h3⟩ := R.lowOK_of w
  have lx : ((R.dlo++R.zA).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have a := LowZero.subLowNC_counts _ _ _ R.cin lx lc (by simp only [List.length_take]; omega)
  have b := subInPlace_counts ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin lx lc
  have c := LowZero.subLowNC_counts _ _ _ R.cin h1 h2 (by omega)
  have d := subInPlace_counts (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin h1 h2
  have em : R.m6w=LowZero.subLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos ⟨h1,h2,h3⟩
  have ez : R.m6z=LowZero.subLowNC (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin := by
    unfold m6z; exact LowZero.subLowNCG_eq _ _ _ _ h1 h2 (by omega)
  rw [em]; rw [ez] at z
  simp only [List.length_take] at a b
  constructor <;> omega

theorem c6w_counts (w : R.W) : toffoliCount R.c6w+2=toffoliCount R.c6 ∧
    measurementCount R.c6w+1=measurementCount R.c6 := by
  have z := R.c6z_counts w
  obtain ⟨h1,h2,h3⟩ := R.lowOK_of w
  have lx : ((R.dlo++R.zA).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have a := LowZero.addLowNC_counts _ _ _ R.cin lx lc (by simp only [List.length_take]; omega)
  have b := addInPlace_counts ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin lx lc
  have c := LowZero.addLowNC_counts _ _ _ R.cin h1 h2 (by omega)
  have d := addInPlace_counts (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin h1 h2
  have em : R.c6w=LowZero.addLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos ⟨h1,h2,h3⟩
  have ez : R.c6z=LowZero.addLowNC (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin := by
    unfold c6z; exact LowZero.addLowNCG_eq _ _ _ _ h1 h2 (by omega)
  rw [em]; rw [ez] at z
  simp only [List.length_take] at a b
  constructor <;> omega

theorem take_headD (l : List Wire) (k : Nat) (hk : 1≤k) : (l.take k).headD 0=l.headD 0 := by
  rcases l with _|⟨a,l⟩
  · simp
  · obtain ⟨j,rfl⟩ : ∃j,k=j+1 := ⟨k-1,by omega⟩
    simp

theorem low_nodup (hn : R.all.Nodup) :
    (R.cin::(((R.dlo++R.zA).take (R.T.length-1))++(R.T.take (R.T.length-1))++
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)))).Nodup := by
  have full : (R.cin::((R.dlo++R.zA)++R.T++(R.carry.take (R.T.length-1)))).Nodup :=
    knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  exact full.sublist ((((List.take_sublist _ _).append (List.take_sublist _ _)).append
    (List.take_sublist _ _)).cons₂ _)

theorem m6w_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (hA : regValue (R.dlo++R.zA) s.basis<2^(R.T.length-1))
    (hb : regValue (R.dlo++R.zA) s.basis≤regValue R.T s.basis%2^(R.T.length-1)) :
    (run R.m6w m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m6w m s).basis q=s.basis q) ∧
    regValue R.T (run R.m6w m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dlo++R.zA) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  obtain ⟨h1,h2,h3⟩ := R.lowOK_of w
  have em : R.m6w=LowZero.subLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos ⟨h1,h2,h3⟩
  have lx : ((R.dlo++R.zA).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have hTn : R.T.Nodup := knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have r := LowZero.subLowNC_correct _ _ _ R.cin (R.low_nodup hn) lx lc (by simp only [List.length_take]; omega) s m
    (fun q h => hcl q (List.mem_of_mem_take h))
    (by rw [take_headD _ _ (by omega),take_headD _ _ (by omega)]; exact hnc) hi
  rw [em]
  refine ⟨r.1,fun q h => r.2.1 q (fun h' => h (List.mem_of_mem_take h')),?_⟩
  set t := run (LowZero.subLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin) m s with ht
  set P := 2^(R.T.length-1) with hP
  have h2P : 2^R.T.length=2*P := by rw [hP,← pow_succ']; congr 1; omega
  have xv : regValue ((R.dlo++R.zA).take (R.T.length-1)) s.basis=regValue (R.dlo++R.zA) s.basis := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega),Nat.mod_eq_of_lt hA]
  have yv : regValue (R.T.take (R.T.length-1)) s.basis=regValue R.T s.basis%P :=
    CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega) _
  have dkeep : regValue (R.T.drop (R.T.length-1)) t.basis=regValue (R.T.drop (R.T.length-1)) s.basis := by
    apply regValue_congr
    intro q hq
    apply r.2.1
    intro hq'
    have := List.disjoint_take_drop hTn (le_refl (R.T.length-1)) hq' hq
    exact this
  have split (st : BasisState) : regValue R.T st=regValue (R.T.take (R.T.length-1)) st+
      P*regValue (R.T.drop (R.T.length-1)) st := by
    have e := regValue_append (R.T.take (R.T.length-1)) (R.T.drop (R.T.length-1)) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by omega)] at e
    exact e
  have dv : regValue (R.T.drop (R.T.length-1)) s.basis=regValue R.T s.basis/P :=
    CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by omega) _
  have tlt : regValue R.T s.basis<2*P := by rw [← h2P]; exact regValue_lt _ _
  have md := Nat.mod_add_div (regValue R.T s.basis) P
  have Ppos : 0<P := by rw [hP]; positivity
  have lowv : regValue (R.T.take (R.T.length-1)) t.basis=regValue R.T s.basis%P-regValue (R.dlo++R.zA) s.basis := by
    rw [r.2.2,xv,yv,hi,Bool.toNat_false,Nat.sub_zero,List.length_take,Nat.min_eq_left (by omega),← hP]
    rw [show regValue R.T s.basis%P+P-regValue (R.dlo++R.zA) s.basis=
      (regValue R.T s.basis%P-regValue (R.dlo++R.zA) s.basis)+P by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (by have := Nat.mod_lt (regValue R.T s.basis) Ppos; omega)]
  rw [split t.basis,lowv,dkeep,dv,hi,Bool.toNat_false,Nat.sub_zero,h2P]
  have mle := Nat.mod_le (regValue R.T s.basis) P
  generalize regValue R.T s.basis%P=M at *
  generalize regValue R.T s.basis/P=D at *
  generalize regValue R.T s.basis=TV at *
  generalize regValue (R.dlo++R.zA) s.basis=AV at *
  have dq : P*D=TV-M := by omega
  rw [dq,show TV+2*P-AV=(TV-AV)+2*P by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  omega

theorem c6w_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (hA : regValue (R.dlo++R.zA) s.basis<2^(R.T.length-1))
    (hb : regValue R.T s.basis%2^(R.T.length-1)+regValue (R.dlo++R.zA) s.basis<2^(R.T.length-1)) :
    (run R.c6w m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c6w m s).basis q=s.basis q) ∧
    regValue R.T (run R.c6w m s).basis=(regValue (R.dlo++R.zA) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  obtain ⟨h1,h2,h3⟩ := R.lowOK_of w
  have em : R.c6w=LowZero.addLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos ⟨h1,h2,h3⟩
  have lx : ((R.dlo++R.zA).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have hTn : R.T.Nodup := knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have r := LowZero.addLowNC_correct _ _ _ R.cin (R.low_nodup hn) lx lc (by simp only [List.length_take]; omega) s m
    (fun q h => hcl q (List.mem_of_mem_take h))
    (by rw [take_headD _ _ (by omega),take_headD _ _ (by omega)]; exact hnc) hi
  rw [em]
  refine ⟨r.1,fun q h => r.2.1 q (fun h' => h (List.mem_of_mem_take h')),?_⟩
  set t := run (LowZero.addLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin) m s with ht
  set P := 2^(R.T.length-1) with hP
  have h2P : 2^R.T.length=2*P := by rw [hP,← pow_succ']; congr 1; omega
  have xv : regValue ((R.dlo++R.zA).take (R.T.length-1)) s.basis=regValue (R.dlo++R.zA) s.basis := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega),Nat.mod_eq_of_lt hA]
  have yv : regValue (R.T.take (R.T.length-1)) s.basis=regValue R.T s.basis%P :=
    CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega) _
  have dkeep : regValue (R.T.drop (R.T.length-1)) t.basis=regValue (R.T.drop (R.T.length-1)) s.basis := by
    apply regValue_congr
    intro q hq
    apply r.2.1
    intro hq'
    exact List.disjoint_take_drop hTn (le_refl (R.T.length-1)) hq' hq
  have split (st : BasisState) : regValue R.T st=regValue (R.T.take (R.T.length-1)) st+
      P*regValue (R.T.drop (R.T.length-1)) st := by
    have e := regValue_append (R.T.take (R.T.length-1)) (R.T.drop (R.T.length-1)) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by omega)] at e
    exact e
  have dv : regValue (R.T.drop (R.T.length-1)) s.basis=regValue R.T s.basis/P :=
    CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by omega) _
  have tlt : regValue R.T s.basis<2*P := by rw [← h2P]; exact regValue_lt _ _
  have md := Nat.mod_add_div (regValue R.T s.basis) P
  have Ppos : 0<P := by rw [hP]; positivity
  have lowv : regValue (R.T.take (R.T.length-1)) t.basis=regValue (R.dlo++R.zA) s.basis+regValue R.T s.basis%P := by
    rw [r.2.2,xv,yv,hi,Bool.toNat_false,Nat.add_zero,List.length_take,Nat.min_eq_left (by omega),← hP]
    exact Nat.mod_eq_of_lt (by omega)
  rw [split t.basis,lowv,dkeep,dv,hi,Bool.toNat_false,Nat.add_zero,h2P]
  have mle := Nat.mod_le (regValue R.T s.basis) P
  have dle : regValue R.T s.basis/P≤1 := by
    have := Nat.div_lt_of_lt_mul (show regValue R.T s.basis<P*2 by omega); omega
  generalize regValue R.T s.basis%P=M at *
  generalize regValue R.T s.basis/P=D at *
  generalize regValue R.T s.basis=TV at *
  generalize regValue (R.dlo++R.zA) s.basis=AV at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp dle with e|e
  · subst e; simp only [Nat.mul_zero,Nat.add_zero] at md ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · subst e; simp only [Nat.mul_one] at md ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem pow_two_mul_split (h : Nat) (hh : 1≤h) : 2^h=2*2^(h-1) := by
  rw [← pow_succ']; congr 1; omega

theorem raw_lo_le (h a : Nat) (hh : 1≤h) (ha : a<2^h) : DiagSq.rawValue h a+2^h≤2^(2*h) := by
  unfold DiagSq.rawValue signedDiagValue
  rw [if_neg (by omega)]
  have hP : 2^h=2*2^(h-1) := pow_two_mul_split h hh
  have hPP : 2^(2*h)=2^h*2^h := by rw [two_mul,pow_add]
  rw [hPP,hP]; rw [hP] at ha
  generalize 2^(h-1)=Q at *
  have Qpos : 0<Q := by omega
  have vlt : a%Q<Q := Nat.mod_lt _ Qpos
  have adiv := Nat.mod_add_div a Q
  obtain ⟨k,hk⟩ : ∃k,Q=a%Q+1+k := ⟨Q-1-a%Q,by omega⟩
  have e1 : Q-1-a%Q=k := by omega
  rw [e1]
  have t1 : a/Q≤1 := by have := Nat.div_lt_of_lt_mul (show a<Q*2 by omega); omega
  generalize a%Q=v at *
  subst hk
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp t1 with e|e
  · have av : a=v := by rw [e] at adiv; omega
    subst av
    nlinarith [Nat.zero_le (a*k),Nat.zero_le (k*k),Nat.zero_le (a*a)]
  · have av : a=v+(v+1+k) := by rw [e] at adiv; omega
    subst av
    nlinarith [Nat.zero_le (v*k),Nat.zero_le (k*k),Nat.zero_le (v*v)]

theorem raw_hi_ge (h S : Nat) (hh : 1≤h) (hS : S<2^(h+1)) :
    2^(2*h)≤DiagSq.rawValue (h+1) S%2^(2*h+1)+2^h := by
  unfold DiagSq.rawValue signedDiagValue
  rw [if_neg (by omega),show h+1-1=h by omega]
  have h1 : 2^(h+1)=2*2^h := by rw [pow_succ]; ring
  have hPP : 2^(2*h)=2^h*2^h := by rw [two_mul,pow_add]
  have hM : 2^(2*h+1)=2*(2^h*2^h) := by rw [pow_succ,hPP]; ring
  rw [h1] at hS ⊢; rw [hPP,hM]
  generalize 2^h=P at *
  have Ppos : 0<P := by omega
  have ult : S%P<P := Nat.mod_lt _ Ppos
  have sdiv := Nat.mod_add_div S P
  obtain ⟨k,hk⟩ : ∃k,P=S%P+1+k := ⟨P-1-S%P,by omega⟩
  have e1 : P-1-S%P=k := by omega
  rw [e1]
  have t1 : S/P≤1 := by have := Nat.div_lt_of_lt_mul (show S<P*2 by omega); omega
  generalize S%P=u at *
  subst hk
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp t1 with e|e
  · have sv : S=u := by rw [e] at sdiv; omega
    subst sv
    have lt : S^2+(S+k*(2*(S+1+k)))<2*((S+1+k)*(S+1+k)) := by
      nlinarith [Nat.zero_le (S*k),Nat.zero_le (k*k),Nat.zero_le (S*S)]
    rw [Nat.mod_eq_of_lt lt]
    nlinarith [Nat.zero_le (S*k),Nat.zero_le (k*k),Nat.zero_le (S*S)]
  · have sv : S=u+(u+1+k) := by rw [e] at sdiv; omega
    subst sv
    have ge : 2*((u+1+k)*(u+1+k))≤(u+(u+1+k))^2+(u+(u+1+k)+k*(2*(u+1+k))) := by
      nlinarith [Nat.zero_le (u*k),Nat.zero_le (k*k),Nat.zero_le (u*u)]
    have lt : (u+(u+1+k))^2+(u+(u+1+k)+k*(2*(u+1+k)))-2*((u+1+k)*(u+1+k))<2*((u+1+k)*(u+1+k)) := by
      have : (u+(u+1+k))^2+(u+(u+1+k)+k*(2*(u+1+k)))<2*((u+1+k)*(u+1+k))+2*((u+1+k)*(u+1+k)) := by
        nlinarith [Nat.zero_le (u*k),Nat.zero_le (k*k),Nat.zero_le (u*u)]
      omega
    rw [Nat.mod_eq_sub_mod ge,Nat.mod_eq_of_lt lt]
    have : (u+1+k)*(u+1+k)+2*((u+1+k)*(u+1+k))≤(u+(u+1+k))^2+(u+(u+1+k)+k*(2*(u+1+k)))+(u+1+k) := by
      nlinarith [Nat.zero_le (u*k),Nat.zero_le (k*k),Nat.zero_le (u*u)]
    omega

/-- The bound used by `m6w`/`c6w`: the subtracted diagonal seed never exceeds the low
`2h+1` bits of the sum-square seed. -/
theorem raw_low_bound (h a b : Nat) (hh : 1≤h) (ha : a<2^h) (hb : b<2^h) :
    DiagSq.rawValue h a≤DiagSq.rawValue (h+1) (a+b)%2^(2*h+1) ∧ DiagSq.rawValue h a<2^(2*h) := by
  have x := raw_lo_le h a hh ha
  have y := raw_hi_ge h (a+b) hh (by rw [pow_succ]; omega)
  have p : 0<2^h := by positivity
  constructor <;> omega

end ECDSAAdd.Entrant.KRegs
end

section
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

theorem subloW_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S TN : Nat) (hX : A<2^R.dlo.length) (hAe : 2∣A) (hT : TN<2^R.T.length)
    (hb : A≤TN%2^(R.T.length-1)) (hA' : A<2^(R.T.length-1)) :
    Transition R base (vec A B S (TN : Int)) (vec A B S ((TN : Int)-A)) R.m6w := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have tv := ht.exact 3 TN rfl hT
  change regValue R.T t.basis=TN at tv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have av : regValue (R.dlo++R.zA) t.basis=A := by rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero]
  have l := R.lo_lens w
  have c := R.m6w_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0) (by rw [av]; exact hA') (by rw [av,tv]; exact hb)
  have r : Update R.T (-(regValue (R.dlo++R.zA) t.basis : Int)) t (run R.m6w rec t) := by
    have vl := regValue_lt (R.dlo++R.zA) t.basis
    rw [l.1] at vl
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.sub_zero]
    simpa only [sub_eq_add_neg] using sub_congr (regValue R.T t.basis) (2^R.T.length)
      (regValue (R.dlo++R.zA) t.basis) (by omega)
  rw [av] at r
  have act := ht.advance hn 3 (-(A : Int)) r
  simpa only [show (vec A B S (TN : Int)) 3=(TN : Int) from rfl,vec3,sub_eq_add_neg] using act

theorem addloW_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (Z : Nat) (hX : A<2^R.dlo.length) (hAe : 2∣A) (hZ : T+A=Z)
    (hZlt : Z<2^R.T.length) (hb : A≤Z%2^(R.T.length-1)) (hA' : A<2^(R.T.length-1)) :
    Transition R base (vec A B S T) (vec A B S (T+A)) R.c6w := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have AZ : A≤Z := le_trans hb (Nat.mod_le _ _)
  have tv := ht.exact 3 (Z-A) (by simp only [vec]; push_cast [AZ]; omega) (by change Z-A<2^R.T.length; omega)
  change regValue R.T t.basis=Z-A at tv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have av : regValue (R.dlo++R.zA) t.basis=A := by rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero]
  have Ppos : 0<2^(R.T.length-1) := by positivity
  have low : (Z-A)%2^(R.T.length-1)+A<2^(R.T.length-1) := by
    have md := Nat.mod_add_div Z (2^(R.T.length-1))
    have ml := Nat.mod_lt Z Ppos
    generalize 2^(R.T.length-1)=P at *
    generalize Z%P=M at *
    generalize Z/P=D at *
    have e : Z-A=(M-A)+P*D := by omega
    rw [e,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega)]
    omega
  have c := R.c6w_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0) (by rw [av]; exact hA') (by rw [av,tv]; exact low)
  have r : Update R.T (regValue (R.dlo++R.zA) t.basis : Int) t (run R.c6w rec t) := by
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.add_zero]
    simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
    rw [Int.add_comm]
    exact Int.emod_emod _ _
  rw [av] at r
  have act := ht.advance hn 3 ((A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

end ECDSAAdd.Entrant.DiagSq
end

namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-- A register whose value is congruent to an even integer modulo `2^len` (`len ≥ 1`) has
its lowest wire clear. -/
theorem head_false_of_modEq (r : List Wire) (st : BasisState) (T : Int) (hl : 1≤r.length)
    (hv : (regValue r st : Int) ≡ T [ZMOD (2^r.length : Nat)]) (hT : (2:Int)∣T) :
    st (r.headD 0)=false := by
  have h2 : (2:Int)∣((2^r.length : Nat) : Int) := by
    push_cast; exact dvd_pow_self 2 (by omega)
  have hd : (2:Int)∣(regValue r st : Int) := by
    have m := (Int.ModEq.dvd hv.symm)
    have := dvd_trans h2 m
    have e : (regValue r st : Int)=T+((regValue r st : Int)-T) := by ring
    rw [e]; exact dvd_add hT this
  obtain ⟨k,hk⟩ := hd
  have hk' : regValue r st=2*k.toNat := by omega
  have ne : r≠[] := by intro e; rw [e] at hl; simp at hl
  have := LowZero.head_false_of_even r [] st k.toNat hk' ne
  simpa using this

theorem addhiZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : B<2^R.dhi.length) (hTe : (2:Int)∣T) :
    Transition R base (vec A B S T) (vec A B S (T+B)) R.c7g := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 1 B rfl hX
  change regValue R.dhi t.basis=B at xv
  have zv := (ht.keep hn R.zB (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zB) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have t0 : t.basis (R.T.headD 0)=false :=
    head_false_of_modEq R.T t.basis T (by omega) (ht.value 3) hTe
  have c := R.c7g_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [t0]; exact Bool.and_false _) ((ht.cin hn).trans hi0)
  have r : Update R.T (regValue (R.dhi++R.zB) t.basis : Int) t (run R.c7g rec t) := by
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.add_zero]
    simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
    rw [Int.add_comm]
    exact Int.emod_emod _ _
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 ((B : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem rawValue_even (n x : Nat) (hn : 1≤n) : 2∣rawValue n x := by
  unfold rawValue signedDiagValue
  rw [if_neg (by omega)]
  have h1 : 2∣x^2+x := by
    rw [show x^2+x=x*(x+1) by ring]; exact (Nat.even_mul_succ_self x).two_dvd
  have h2 : 2∣(2^(n-1)-1-x%2^(n-1))*2^n := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
  rw [show x^2+(x+(2^(n-1)-1-x%2^(n-1))*2^n)=(x^2+x)+(2^(n-1)-1-x%2^(n-1))*2^n by ring]
  exact dvd_add h1 h2

theorem subloZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : A<2^R.dlo.length) (hAe : 2∣A) :
    Transition R base (vec A B S T) (vec A B S (T-A)) R.m6z := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have l := R.lo_lens w
  have c := R.m6z_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0)
  have r : Update R.T (-(regValue (R.dlo++R.zA) t.basis : Int)) t (run R.m6z rec t) := by
    have vl := regValue_lt (R.dlo++R.zA) t.basis
    rw [l.1] at vl
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.sub_zero]
    simpa only [sub_eq_add_neg] using sub_congr (regValue R.T t.basis) (2^R.T.length)
      (regValue (R.dlo++R.zA) t.basis) (by omega)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 (-(A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem subhiZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : B<2^R.dhi.length) (hBe : 2∣B) :
    Transition R base (vec A B S T) (vec A B S (T-B)) R.m7g := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 1 B rfl hX
  change regValue R.dhi t.basis=B at xv
  have zv := (ht.keep hn R.zB (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zB) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dhi++R.zB).headD 0)=false := by
    obtain ⟨k,hk⟩ := hBe
    exact LowZero.head_false_of_even R.dhi R.zB t.basis k (by rw [xv,hk]) (R.dhi_neg w)
  have l := R.t_lensg w
  have c := R.m7g_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0)
  have r : Update R.T (-(regValue (R.dhi++R.zB) t.basis : Int)) t (run R.m7g rec t) := by
    have vl := regValue_lt (R.dhi++R.zB) t.basis
    rw [l.1] at vl
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.sub_zero]
    simpa only [sub_eq_add_neg] using sub_congr (regValue R.T t.basis) (2^R.T.length)
      (regValue (R.dhi++R.zB) t.basis) (by omega)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 (-(B : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem addloZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : A<2^R.dlo.length) (hAe : 2∣A) :
    Transition R base (vec A B S T) (vec A B S (T+A)) R.c6z := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have c := R.c6z_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0)
  have r : Update R.T (regValue (R.dlo++R.zA) t.basis : Int) t (run R.c6z rec t) := by
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.add_zero]
    simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
    rw [Int.add_comm]
    exact Int.emod_emod _ _
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 ((A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act


theorem head_eq_of_modEq (r r' : List Wire) (st : BasisState) (T : Int) (hl : 1≤r.length) (hl' : 1≤r'.length)
    (hv : (regValue r st : Int) ≡ T [ZMOD (2^r.length : Nat)]) (hT : (2:Int)∣T-regValue r' st) :
    st (r.headD 0)=st (r'.headD 0) := by
  have h2 : (2:Int)∣((2^r.length : Nat) : Int) := by
    push_cast; exact dvd_pow_self 2 (by omega)
  have d1 : (2:Int)∣(regValue r st : Int)-T := dvd_trans h2 (Int.ModEq.dvd hv.symm)
  have d : (2:Int)∣(regValue r st : Int)-regValue r' st := by
    have e : (regValue r st : Int)-regValue r' st=((regValue r st : Int)-T)+(T-regValue r' st) := by ring
    rw [e]; exact dvd_add d1 hT
  have ne : r≠[] := by intro e; rw [e] at hl; simp at hl
  have ne' : r'≠[] := by intro e; rw [e] at hl'; simp at hl'
  have a := LowZero.head_bit r [] st ne
  have b := LowZero.head_bit r' [] st ne'
  simp only [List.append_nil] at a b
  rw [a,b]
  have : regValue r st%2=regValue r' st%2 := by omega
  rw [this]

theorem sq_sub_even (a : Nat) : (2:Int)∣((a^2 : Nat) : Int)-(a : Int) := by
  have h : 2∣a^2+a := by
    rw [show a^2+a=a*(a+1) by ring]; exact (Nat.even_mul_succ_self a).two_dvd
  have h' : (2:Int)∣((a^2+a : Nat) : Int) := by exact_mod_cast h
  push_cast at h' ⊢
  have e : (a:Int)^2-a=((a:Int)^2+a)-2*a := by ring
  rw [e]; exact dvd_sub h' (dvd_mul_right 2 _)

theorem dsubloZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hAe : (2:Int)∣A) :
    Transition R base (vec A B S T) (vec (A-(signedDiagValue (regValue R.lo base.basis) R.h : Nat)) B S T)
      (dSubZ R.lo R.dlo R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have e := dSubZ_run R.lo R.dlo R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    ((ht.cin hn).trans hi0) (head_false_of_modEq R.dlo t.basis A (by omega) (ht.value 0) hAe)
  rw [e]
  exact diagsublo_transition R w he hn base hc0 hi0 A B S T t rec ht

theorem dsubhiZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hBe : (2:Int)∣B) :
    Transition R base (vec A B S T) (vec A (B-(signedDiagValue (regValue R.hi base.basis) R.h : Nat)) S T)
      (dSubZ R.hi R.dhi R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have e := dSubZ_run R.hi R.dhi R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    ((ht.cin hn).trans hi0) (head_false_of_modEq R.dhi t.basis B (by omega) (ht.value 1) hBe)
  rw [e]
  exact diagsubhi_transition R w he hn base hc0 hi0 A B S T t rec ht

theorem daddloZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hAp : (2:Int)∣A-regValue R.lo base.basis) :
    Transition R base (vec A B S T) (vec (A+(signedDiagValue (regValue R.lo base.basis) R.h : Nat)) B S T)
      (dAddZ R.lo R.dlo R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have hb := head_eq_of_modEq R.dlo R.lo t.basis A (by omega) (by omega) (ht.value 0) (by rw [xv]; exact hAp)
  have e := dAddZ_run R.lo R.dlo R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    ((ht.cin hn).trans hi0) (by
      intro y ys' ey hx
      have h1 : t.basis (R.dlo.headD 0)=true := by rw [hb]; exact hx
      rw [ey] at h1; simpa using h1)
  rw [e]
  exact diagaddlo_transition R w he hn base hc0 hi0 A B S T t rec ht

theorem daddhiZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hBp : (2:Int)∣B-regValue R.hi base.basis) :
    Transition R base (vec A B S T) (vec A (B+(signedDiagValue (regValue R.hi base.basis) R.h : Nat)) S T)
      (dAddZ R.hi R.dhi R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have hb := head_eq_of_modEq R.dhi R.hi t.basis B (by omega) (by omega) (ht.value 1) (by rw [xv]; exact hBp)
  have e := dAddZ_run R.hi R.dhi R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    ((ht.cin hn).trans hi0) (by
      intro y ys' ey hx
      have h1 : t.basis (R.dhi.headD 0)=true := by rw [hb]; exact hx
      rw [ey] at h1; simpa using h1)
  rw [e]
  exact diagaddhi_transition R w he hn base hc0 hi0 A B S T t rec ht

def headBlockZ (R : KRegs) : Program := seedsT R ++ (R.m6w++R.m7g++corrZ R++
  dSubZ R.lo R.dlo R.carry R.cin++dSubZ R.hi R.dhi R.carry R.cin)

/-- `make` with the dead lowest carries of `m6`, `m7`, `m8` dropped. -/
def makeZ (R : KRegs) : Program := headBlockZ R++R.m8g

theorem makeZ_counts_rel (R : KRegs) (w : R.W) :
    toffoliCount (makeZ R)+10=toffoliCount (make R) ∧ measurementCount (makeZ R)+4=measurementCount (make R) := by
  have a := R.m6w_counts w; have b := R.m7g_counts w; have c := R.m8g_counts w
  have cz := corrZ_counts R w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hdl := w.dst; have hpl := w.pad; have hh := w.hh; have h5 := w.h5
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have ds1 := dSubZ_counts R.lo R.dlo R.carry R.cin (by omega) (by omega) (by omega)
  have ds2 := dSubZ_counts R.hi R.dhi R.carry R.cin (by omega) (by omega) (by omega)
  have t1 := rawT_counts R.lo R.dlo R.pad R.carry (by simp only [KRegs.lo,List.length_take]; omega)
    (by simp only [KRegs.lo,KRegs.dlo,List.length_take]; omega) hpl
    (by simp only [KRegs.lo,List.length_take]; omega)
  have t2 := rawT_counts R.hi R.dhi R.pad R.carry (by simp only [KRegs.hi,List.length_drop]; omega)
    (by simp only [KRegs.hi,KRegs.dhi,List.length_drop]; omega) hpl
    (by simp only [KRegs.hi,List.length_drop]; omega)
  have t5 := rawT_counts R.S R.T R.pad R.carry (by omega) (by omega) hpl (by omega)
  simp only [makeZ,make,headBlockZ,headBlock,seedsT,seeds,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem makeZ_counts (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (makeZ R)+10=cost R ∧ measurementCount (makeZ R)+4=cost R := by
  have a := makeZ_counts_rel R w
  have b := make_counts R w he
  constructor <;> omega

theorem rawMakeT_wires_sub (xs dst pad carry : List Wire) :
    wires (rawMakeT xs dst pad carry)⊆wires (rawMake xs dst pad carry) := by
  unfold rawMakeT rawMake; exact (ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry).1

theorem seedsT_wires (R : KRegs) : wires (seedsT R)⊆wires (seeds R) := by
  simp only [seedsT,seeds,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union
    (rawMakeT_wires_sub _ _ _ _) (rawMakeT_wires_sub _ _ _ _)) (subset_refl _)) (rawMakeT_wires_sub _ _ _ _)

theorem makeZ_support (R : KRegs) (w : R.W) : wires (makeZ R)⊆R.all.toFinset := by
  have old := (steps_support R w).1
  have a := R.m6w_wires; have b := R.m7g_wires; have c := R.m8g_wires
  have d := seedsT_wires R
  simp only [make,headBlock,wires_append,Finset.union_subset_iff] at old
  simp only [makeZ,headBlockZ,wires_append,Finset.union_subset_iff]
  obtain ⟨⟨o1,⟨⟨⟨⟨o2,o3⟩,o4⟩,o5⟩,o6⟩⟩,o7⟩ := old
  exact ⟨⟨d.trans o1,⟨⟨⟨⟨a.trans o2,b.trans o3⟩,(wires_of_mem (corrZ_mem R)).trans o4⟩,(wires_of_mem (dSubZ_mem _ _ _ _)).trans o5⟩,(wires_of_mem (dSubZ_mem _ _ _ _)).trans o6⟩⟩,c.trans o7⟩

theorem makeZ_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (makeZ R) := by
  have old := (steps_physical R w hn).1
  have oldc := (steps_physical R w hn).2
  simp only [make,headBlock,seeds,rawMake,gatePhysical_append] at old
  simp only [clear,rawClear,gatePhysical_append] at oldc
  simp only [makeZ,headBlockZ,seedsT,gatePhysical_append]
  obtain ⟨⟨⟨⟨⟨⟨l1,l2⟩,⟨h1,h2⟩⟩,sm⟩,⟨s1,s2⟩⟩,⟨⟨⟨⟨o2,o3⟩,o4⟩,o5⟩,o6⟩⟩,o7⟩ := old
  have pl := ECDSAAdd.Entrant.TrimRow.physical R.lo R.dlo R.pad R.carry
    (by rw [gatePhysical_append]; exact ⟨l1,l2⟩) (by rw [gatePhysical_append]; exact ⟨l2,by tauto⟩)
  have ph := ECDSAAdd.Entrant.TrimRow.physical R.hi R.dhi R.pad R.carry
    (by rw [gatePhysical_append]; exact ⟨h1,h2⟩) (by rw [gatePhysical_append]; exact ⟨h2,by tauto⟩)
  have ps := ECDSAAdd.Entrant.TrimRow.physical R.S R.T R.pad R.carry
    (by rw [gatePhysical_append]; exact ⟨s1,s2⟩) (by rw [gatePhysical_append]; exact ⟨s2,by tauto⟩)
  exact ⟨⟨⟨⟨⟨pl.1,ph.1⟩,sm⟩,ps.1⟩,⟨⟨⟨⟨R.m6w_physical hn,R.m7g_physical hn⟩,(fun i hi => o4 i (corrZ_mem R i hi))⟩,(fun i hi => o5 i (dSubZ_mem _ _ _ _ i hi))⟩,(fun i hi => o6 i (dSubZ_mem _ _ _ _ i hi))⟩⟩,R.m8g_physical hn⟩

theorem makeZ_slots (R : KRegs) : Challenge.gateSlots (makeZ R)≤Challenge.gateSlots (make R) := by
  have a := R.m6w_slots; have b := R.m7g_slots; have c := R.m8g_slots; have cz := corrZ_slots R
  have ds1 := dSubZ_slots R.lo R.dlo R.carry R.cin; have ds2 := dSubZ_slots R.hi R.dhi R.carry R.cin
  have t1 := (ECDSAAdd.Entrant.TrimRow.slots R.lo R.dlo R.pad R.carry).1
  have t2 := (ECDSAAdd.Entrant.TrimRow.slots R.hi R.dhi R.pad R.carry).1
  have t5 := (ECDSAAdd.Entrant.TrimRow.slots R.S R.T R.pad R.carry).1
  simp only [makeZ,make,headBlockZ,headBlock,seedsT,seeds,rawMakeT,rawMake,Challenge.gateSlots_append] at t1 t2 t5 ⊢
  omega

theorem prefixZ_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (headBlockZ R) m s)
      (vec ((regValue R.lo s.basis)^2) ((regValue R.hi s.basis)^2)
        (regValue R.lo s.basis+regValue R.hi s.basis) (2*regValue R.lo s.basis*regValue R.hi s.basis)) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4
  have hhi : R.hi.length=R.h := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let A := rawValue R.h a
  let B := rawValue R.h b
  let S := a+b
  let Z := rawValue (R.h+1) S
  have hA : A<2^R.dlo.length := by
    have v := rawValue_bound R.lo s.basis (by omega)
    simpa only [L0,L2] using v
  have hB : B<2^R.dhi.length := by
    have v := rawValue_bound R.hi s.basis (by omega)
    simpa only [hhi,L3,show 2*(R.bank.length-R.h)=2*R.h by omega] using v
  have alo : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bhi : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have bnd := KRegs.raw_low_bound R.h a b (by omega) alo bhi
  have hT1 : R.T.length=2*R.h+2 := by have := w.T; have := w.S; omega
  have zlt : Z<2^(2*R.h+2) := by
    have x := KRegs.raw_lo_le (R.h+1) S (by omega) (by rw [pow_succ]; dsimp only [S]; omega)
    rw [show 2*(R.h+1)=2*R.h+2 by ring] at x
    exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (by positivity)) x
  have p2 : 2^(2*R.h)≤2^(2*R.h+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb1 : A≤Z%2^(R.T.length-1) := by rw [hT1,show 2*R.h+2-1=2*R.h+1 by omega]; exact bnd.1
  have hA1 : A<2^(R.T.length-1) := by rw [hT1,show 2*R.h+2-1=2*R.h+1 by omega]; exact lt_of_lt_of_le bnd.2 p2
  have hZ1 : Z<2^R.T.length := by rw [hT1]; exact zlt
  have st1 := subloW_transition R w hn s hz0 hc0 hi0 A B S Z hA (rawValue_even _ _ (by omega)) hZ1 hb1 hA1
  have st2 := subhiZ_transition R w hn s hz0 hc0 hi0 A B S ((Z : Int)-A) hB (rawValue_even _ _ (by omega))
  have st3 := corrZ_transition R w he hh hn s hz0 hc0 hi0 A B ((Z : Int)-A-B)
  have norm := cross_normalize R.h a b hh alo bhi
  change ((Z : Nat) : Int)-A-B-((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)+(2^(2*R.h-1) : Nat)=
    (2*a*b : Nat) at norm
  rw [norm] at st3
  have st4 := dsubloZ_transition R w he hn s hc0 hi0 A B S (2*a*b : Nat) (by exact_mod_cast rawValue_even _ _ (by omega))
  have st4' : Transition R s (vec A B S (2*a*b : Nat)) (vec (a^2 : Nat) B S (2*a*b : Nat))
      (dSubZ R.lo R.dlo R.carry R.cin) := by
    simpa only [A,a,rawValue,Int.natCast_add,add_sub_cancel_right] using st4
  have st5 := dsubhiZ_transition R w he hn s hc0 hi0 (a^2 : Nat) B S (2*a*b : Nat) (by exact_mod_cast rawValue_even _ _ (by omega))
  have st5' : Transition R s (vec (a^2 : Nat) B S (2*a*b : Nat))
      (vec (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat))
      (dSubZ R.hi R.dhi R.carry R.cin) := by
    simpa only [B,b,rawValue,Int.natCast_add,add_sub_cancel_right] using st5
  have tail := (((st1.seq st2).seq st3).seq st4').seq st5'
  have initial := seedsT_shape R w he hn s (m.take (measurementCount (seedsT R))) hd0 hS0 hT0 hz0 hp0 hc0 hi0
  have result := tail _ (m.drop (measurementCount (seedsT R))) initial
  simpa only [headBlockZ,run_append,A,B,S,Z,a,b,Int.natCast_mul,Int.natCast_add,Int.natCast_pow] using result


theorem makeZ_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (makeZ R) m s).phase=s.phase ∧
    regValue R.dst (run (makeZ R) m s).basis=(regValue R.bank s.basis)^2 ∧
    regValue R.S (run (makeZ R) m s).basis=regValue R.lo s.basis+regValue R.hi s.basis ∧
    regValue R.T (run (makeZ R) m s).basis=2*regValue R.lo s.basis*regValue R.hi s.basis ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (makeZ R) m s).basis q=s.basis q := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let f := m.take (measurementCount (headBlockZ R))
  let g := m.drop (measurementCount (headBlockZ R))
  let u := run (headBlockZ R) f s
  have h := prefixZ_shape R w he hh hn s f hd0 hS0 hT0 hz0 hp0 hc0 hi0
  have al : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bl : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have slt : a+b<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [a,b]; omega
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  have sq := square_bound (a+b) R.S.length slt
  have tvlt : 2*a*b<2^R.T.length := by rw [hTl]; omega
  have av : regValue R.dlo u.basis=a^2 := h.exact 0 (a^2) (by simp [vec,a,b])
    (by change a^2<2^R.dlo.length; rw [L2]; exact square_bound _ _ al)
  have bv : regValue R.dhi u.basis=b^2 := h.exact 1 (b^2) (by simp [vec,a,b])
    (by change b^2<2^R.dhi.length; rw [L3,show R.bank.length-R.h=R.h by omega]; exact square_bound _ _ bl)
  have sv : regValue R.S u.basis=a+b := h.exact 2 (a+b) (by simp [vec,a,b]) slt
  have tv : regValue R.T u.basis=2*a*b := h.exact 3 (2*a*b) (by simp [vec,a,b]) tvlt
  have dv : regValue R.dst u.basis=a^2+2^(2*R.h)*b^2 := by rw [R.dst_value w,av,bv]
  have cv := (h.keep hn R.carry (by intro q hq; simp [hq])).trans hc0
  have zv := (h.keep hn R.zM (fun q hq => Or.inr (Or.inl (List.mem_of_mem_take hq)))).trans
    (KRegs.xz (r:=R.zM) hz0 (fun q hq => List.mem_of_mem_take hq))
  have r := R.m8g_correct w hn u g (a*b) (fun q hq => (regValue_zero _ _).mp cv q (List.mem_of_mem_take hq))
    (by rw [tv]; ring) ((h.cin hn).trans hi0)
  have rv : regValue R.dmid (run R.m8g g u).basis=
      (2*a*b+(a^2+2^(2*R.h)*b^2)/2^R.h)%2^(2*R.bank.length-R.h) := by
    rw [r.2.2,regValue_append,tv,zv,h.cin hn,hi0,
      show regValue R.dmid u.basis=regValue R.dst u.basis/2^R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by have := w.dst; omega) u.basis,dv,L4]
    simp
  have frame : ∀q,q∉R.dmid → (run R.m8g g u).basis q=u.basis q := r.2.1
  have keepLow : regValue (R.dst.take R.h) (run R.m8g g u).basis=regValue (R.dst.take R.h) u.basis :=
    kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)
  have dfin : regValue R.dst (run R.m8g g u).basis=(regValue R.bank s.basis)^2 := by
    rw [R.bank_value w s.basis,R.dst_value_mid w,rv,keepLow,
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst R.h (by have := w.dst; omega),dv]
    exact KRegs.kfinal a b R.h R.bank.length al (by simpa only [show R.bank.length-R.h=R.h by omega] using bl) (by omega)
  have result : (run R.m8g g u).phase=s.phase ∧ regValue R.dst (run R.m8g g u).basis=(regValue R.bank s.basis)^2 ∧
      regValue R.S (run R.m8g g u).basis=a+b ∧ regValue R.T (run R.m8g g u).basis=2*a*b ∧
      ∀q,q∉R.dst → q∉R.S → q∉R.T → (run R.m8g g u).basis q=s.basis q := by
    refine ⟨r.1.trans h.phase,dfin,?_,?_,?_⟩
    · exact (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans sv
    · exact (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans tv
    · intro q hd hs ht
      exact (frame q (fun bad => hd (List.mem_of_mem_drop bad))).trans (h.rest q hd hs ht)
  simpa only [makeZ,run_append,u,f,g,a,b] using result

theorem clearZ_start_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run R.c8g m s) (vec ((regValue R.lo s.basis)^2 : Nat) ((regValue R.hi s.basis)^2 : Nat)
      (regValue R.lo s.basis+regValue R.hi s.basis : Nat) (2*regValue R.lo s.basis*regValue R.hi s.basis : Nat)) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry; have hdl := w.dst
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  have al : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bl : b<2^(R.bank.length-R.h) := by simpa only [L1] using regValue_lt R.hi s.basis
  have av : a^2<2^(2*R.h) := square_bound _ _ al
  have hd : regValue R.dst s.basis=(a+2^R.h*b)^2 := by
    simpa only [R.bank_value w s.basis] using hd0
  have XLt : (a+2^R.h*b)^2<2^(2*R.bank.length) := by
    rw [←R.bank_value w s.basis]
    exact square_bound _ _ (regValue_lt R.bank s.basis)
  have hX : (a+2^R.h*b)^2=(a^2+2^(2*R.h)*b^2)+2^R.h*(2*a*b) := by ring
  have hdiv : (a+2^R.h*b)^2/2^R.h=(a^2+2^(2*R.h)*b^2)/2^R.h+2*a*b := by
    rw [hX,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  have hmod : (a+2^R.h*b)^2%2^R.h=(a^2+2^(2*R.h)*b^2)%2^R.h := by
    rw [hX,Nat.add_mul_mod_self_left]
  have hq : (a+2^R.h*b)^2/2^R.h<2^(2*R.bank.length-R.h) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),←pow_add,
      show 2*R.bank.length-R.h+R.h=2*R.bank.length by omega]
    exact XLt
  have r := R.c8g_correct w hn s m (fun q hq => (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq))
    (by rw [LowZero.head_false_of_even R.T R.zM s.basis (a*b) (by rw [hT0]; ring) (R.T_neg w)]; rfl) hi0
  have frame : ∀q,q∉R.dmid → (run R.c8g m s).basis q=s.basis q := r.2.1
  have low : regValue (R.dst.take R.h) (run R.c8g m s).basis=regValue (R.dst.take R.h) s.basis := kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)
  have zm : regValue R.zM s.basis=0 := KRegs.xz hz0 (fun q h => List.mem_of_mem_take h)
  have dv : regValue R.dst (run R.c8g m s).basis=a^2+2^(2*R.h)*b^2 := by
    rw [R.dst_value_mid w,
      r.2.2,low,regValue_append,hT0,zm,hi0,
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst R.h (by omega),
      show regValue R.dmid s.basis=regValue R.dst s.basis/2^R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by omega) s.basis,hd,L4]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [hdiv]; exact Nat.le_add_left _ _) hq,hdiv,hmod,Nat.add_sub_cancel,Nat.mod_add_div]
  have dlo : regValue R.dlo (run R.c8g m s).basis=a^2 := by
    rw [show regValue R.dlo (run R.c8g m s).basis=regValue R.dst (run R.c8g m s).basis%2^(2*R.h) from
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst (2*R.h) (by omega) _,dv,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt av]
  have dhi : regValue R.dhi (run R.c8g m s).basis=b^2 := by
    rw [show regValue R.dhi (run R.c8g m s).basis=regValue R.dst (run R.c8g m s).basis/2^(2*R.h) from
      CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst (2*R.h) (by omega) _,dv,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt av,Nat.zero_add]
  have sv := (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans hS0
  have tv := (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans hT0
  refine ⟨r.1,?_,fun q hd _ _ => frame q (fun bad => hd (List.mem_of_mem_drop bad))⟩
  intro i; fin_cases i
  · change (regValue R.dlo _ : Int) ≡ _ [ZMOD _]
    rw [dlo]; exact Int.ModEq.rfl
  · change (regValue R.dhi _ : Int) ≡ _ [ZMOD _]
    rw [dhi]; exact Int.ModEq.rfl
  · change (regValue R.S _ : Int) ≡ _ [ZMOD _]
    rw [sv]; exact Int.ModEq.rfl
  · change (regValue R.T _ : Int) ≡ _ [ZMOD _]
    rw [tv]; exact Int.ModEq.rfl


end ECDSAAdd.Entrant.DiagSq


namespace ECDSAAdd.Entrant.Z5Diagonal
open Arithmetic DiagSq KRegs

def clear (R : KRegs) : Program := R.c8g++(dAddZ R.lo R.dlo R.carry R.cin++
  dAddZ R.hi R.dhi R.carry R.cin++corrBackZ R++R.c7g++R.c6w++
  rawClearT R.S R.T R.pad R.carry++R.scl1591++rawClearT R.hi R.dhi R.pad R.carry++
  rawClearT R.lo R.dlo R.pad R.carry)

def makeC (R : KRegs) : Program := DiagSq.makeZ R++R.scl1591
def clearC (R : KRegs) : Program := R.smk++clear R

theorem clearSum_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (base : State) (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0)
    (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B 0 T) R.scl1591 := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hs := w.S
  have hl : R.hi.length=R.h := by omega
  have av := regValue_lt R.lo base.basis; have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hl] at bv
  have hS : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [show R.S.length=R.h+1 by omega,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) hS
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have r := R.scl1591_correct w hn t rec (by rw [sv,al,bl])
    ((ht.keep hn R.z (by intro q h; simp [h])).trans hz0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0) ((ht.cin hn).trans hi0)
  have val : (regValue (reg R 2) (run R.scl1591 rec t).basis : Int) ≡ 0 [ZMOD (2^(reg R 2).length : Nat)] := by
    change (regValue R.S _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec2] using ht.step hn 2 0 r.1 r.2.2 val


theorem clear_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (clear R) m s).phase=s.phase ∧
    regValue R.dst (run (clear R) m s).basis=0 ∧
    regValue R.S (run (clear R) m s).basis=0 ∧
    regValue R.T (run (clear R) m s).basis=0 ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (clear R) m s).basis q=s.basis q := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let A := rawValue R.h a
  let B := rawValue R.h b
  let S := a+b
  let Z := rawValue (R.h+1) S
  let d : Int := ((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)-(2^(2*R.h-1) : Nat)
  have alo : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bhi : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have hA : A<2^R.dlo.length := by
    have v := rawValue_bound R.lo s.basis (by omega)
    simpa only [L0,L2] using v
  have hB : B<2^R.dhi.length := by
    have v := rawValue_bound R.hi s.basis (by omega)
    simpa only [hhi,L3,show 2*(R.bank.length-R.h)=2*R.h by omega] using v
  have slt : S<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [S]; omega
  have st1 := daddloZ_transition R w he hn s hc0 hi0 (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat) (sq_sub_even a)
  have st1' : Transition R s (vec (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat))
      (vec A (b^2 : Nat) S (2*a*b : Nat)) (dAddZ R.lo R.dlo R.carry R.cin) := by
    simpa only [A,a,rawValue,Int.natCast_add] using st1
  have st2 := daddhiZ_transition R w he hn s hc0 hi0 A (b^2 : Nat) S (2*a*b : Nat) (sq_sub_even b)
  have st2' : Transition R s (vec A (b^2 : Nat) S (2*a*b : Nat))
      (vec A B S (2*a*b : Nat)) (dAddZ R.hi R.dhi R.carry R.cin) := by
    simpa only [B,b,rawValue,Int.natCast_add] using st2
  have st3 := corrBackZ_transition R w he hh hn s hz0 hc0 hi0 A B (2*a*b : Nat)
  have st4 := addhiZ_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d) hB (by
    apply dvd_add
    · push_cast; exact ⟨(a:Int)*b, by ring⟩
    · dsimp only [d]
      apply dvd_sub
      · apply Dvd.dvd.mul_right
        push_cast; exact dvd_pow_self 2 (by omega)
      · push_cast; exact dvd_pow_self 2 (by omega))
  have norm := cross_normalize R.h a b hh alo bhi
  have norm' : ((2*a*b : Nat) : Int)+d+B+A=Z := by
    change ((Z : Nat) : Int)-A-B-((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)+(2^(2*R.h-1) : Nat)=
      (2*a*b : Nat) at norm
    dsimp only [d]
    linarith only [norm]
  have bnd := KRegs.raw_low_bound R.h a b (by omega) alo bhi
  have hT1 : R.T.length=2*R.h+2 := by have := w.T; have := w.S; omega
  have zlt : Z<2^(2*R.h+2) := by
    have x := KRegs.raw_lo_le (R.h+1) S (by omega) (by rw [pow_succ]; dsimp only [S]; omega)
    rw [show 2*(R.h+1)=2*R.h+2 by ring] at x
    exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (by positivity)) x
  have p2 : 2^(2*R.h)≤2^(2*R.h+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb1 : A≤Z%2^(R.T.length-1) := by rw [hT1,show 2*R.h+2-1=2*R.h+1 by omega]; exact bnd.1
  have hA1 : A<2^(R.T.length-1) := by rw [hT1,show 2*R.h+2-1=2*R.h+1 by omega]; exact lt_of_lt_of_le bnd.2 p2
  have hZ1 : Z<2^R.T.length := by rw [hT1]; exact zlt
  have st5 := addloW_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d+B) Z hA (rawValue_even _ _ (by omega)) norm' hZ1 hb1 hA1
  rw [norm'] at st5
  have st6 := rawclearSum_transitionT R w hn s hp0 hc0 A B S slt
  rw [hSS] at st6
  have st7 := clearSum_transition R w he hn s hz0 hc0 hi0 A B 0
  have st8 := rawclearhi_transitionT R w he hn s hp0 hc0 A 0 0
  have st9 := rawclearlo_transitionT R w he hn s hp0 hc0 0 0 0
  have st3' : Transition R s (vec A B S (2*a*b : Nat))
      (vec A B S ((2*a*b : Nat)+d)) (corrBackZ R) := by
    (convert st3 using 1; try rfl)
    simp only [d]
    congr 1
    ring
  have tail := ((((((((st1'.seq st2').seq st3').seq st4).seq st5).seq st6).seq st7).seq st8).seq st9)
  have initial := clearZ_start_shape R w he hn s (m.take (measurementCount R.c8g)) hd0 hS0 hT0 hz0 hc0 hi0
  have result := tail _ (m.drop (measurementCount R.c8g)) initial
  have final : Shape R s (run (clear R) m s) (vec 0 0 0 0) := by
    simpa only [clear,run_append] using result
  refine ⟨final.phase,?_,final.exact 2 0 rfl (by norm_num),final.exact 3 0 rfl (by norm_num),final.rest⟩
  have zlo : regValue R.dlo (run (clear R) m s).basis=0 := final.exact 0 0 rfl (by norm_num)
  have zhi : regValue R.dhi (run (clear R) m s).basis=0 := final.exact 1 0 rfl (by norm_num)
  rw [R.dst_value w,zlo,zhi]
  simp

variable (R : KRegs)

theorem diag_sq_full_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (DiagSq.makeZ R) R.invF := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  have r := DiagSq.makeZ_correct R w he hh hn s m hd0 (xz hX (fun q h => List.mem_append_left _ h))
    (xz hX (fun q h => List.mem_append_right _ h)) (xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [invF,r.2.2.1,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  exact ⟨rfl,rfl⟩

theorem diag_sq_full_clear (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqClear R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (clear R) R.invF := by
  intro s m hd0 hI hp0 hc0 hz0 hi0
  have r := clear_correct R w he hh hn s m hd0 (by rw [hI.1,R.lo_mod w,R.hi_div w]) (by rw [hI.2,R.lo_mod w,R.hi_div w])
    (xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [regValue_append,r.2.2.1,r.2.2.2.1]; simp

theorem diag_sq_cl_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (makeC R) R.invC := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  let a := m.take (measurementCount (DiagSq.makeZ R))
  let b := m.drop (measurementCount (DiagSq.makeZ R))
  have r := DiagSq.makeZ_correct R w he hh hn s a hd0 (xz hX (fun q h => List.mem_append_left _ h))
    (xz hX (fun q h => List.mem_append_right _ h)) (xz hz0 hz) hp0 hc0 hi0
  generalize hu : run (DiagSq.makeZ R) a s=u at r
  have fu : ∀q,q∉R.S → q∉R.T → q∉R.dst → u.basis q=s.basis q := fun q a b c => r.2.2.2.2 q c a b
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S ∧ q∉R.T ∧ q∉R.dst) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => fu q (hl q hq).1 (hl q hq).2.1 (hl q hq).2.2)
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin) : q∉R.S ∧ q∉R.T ∧ q∉R.dst :=
    let x := R.outside hn q h; ⟨x.2.1,x.2.2,x.1⟩
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := R.scl1591_correct w hn u b (by rw [r.2.2.1,lo,hi])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((fu _ (o _ (by simp)).1 (o _ (by simp)).2.1 (o _ (by simp)).2.2).trans hi0)
  have eq : run (makeC R) m s=run R.scl1591 b u := by
    rw [makeC,run_append,←hu]
  rw [eq]
  have sT := R.outside hn
  have dS : ∀q∈R.dst,q∉R.S := kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega)
  have TS : ∀q∈R.T,q∉R.S := kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega)
  refine ⟨c.1.trans r.1,?_,?_,?_⟩
  · rw [kkeep c.2.2 dS,r.2.1]
  · refine ⟨c.2.1,?_⟩
    rw [kkeep c.2.2 TS,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2 q xS).trans (fu q xS xT h)

theorem diag_sq_cl_clear (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqClear R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (clearC R) R.invC := by
  intro s m hd0 hI hp0 hc0 hz0 hi0
  let a := m.take (measurementCount R.smk)
  let b := m.drop (measurementCount R.smk)
  have r := R.smk_correct w hn s a hI.1 (xz hz0 hz) hc0 hi0
  generalize hu : run R.smk a s=u at r
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin ∨ q∈R.dst ∨ q∈R.T) : q∉R.S := by
    rcases h with h|h|h|h|h|h|h
    · exact (R.outside hn q (Or.inl h)).2.1
    · exact (R.outside hn q (Or.inr (Or.inl h))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inl h)))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inr (Or.inl h))))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inr (Or.inr h))))).2.1
    · exact kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega) q h
    · exact kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega) q h
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => r.2.2 q (hl q hq))
  have bk := keep R.bank (fun q h => o q (Or.inl h))
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := clear_correct R w he hh hn u b (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),bk]; exact hd0)
    (by rw [r.2.1,lo,hi])
    (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))),hI.2,lo,hi,R.lo_mod w,R.hi_div w])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inl h))))).trans hp0)
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((r.2.2 _ (o _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).trans hi0)
  have eq : run (clearC R) m s=run (clear R) b u := by
    rw [clearC,run_append,←hu]
  rw [eq]
  refine ⟨c.1.trans r.1,c.2.1,?_,?_⟩
  · rw [regValue_append,c.2.2.1,c.2.2.2.1]; simp
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2.2.2 q h xS xT).trans (r.2.2 q xS)


theorem clear_counts_diff (R : KRegs) (w : R.W) :
    toffoliCount (clear R)+(R.bank.length-R.h)+10=toffoliCount (DiagSq.clear R) ∧
    measurementCount (clear R)+4=measurementCount (DiagSq.clear R) := by
  have a := R.piece_counts w
  have b := R.scl1591_counts w
  have z8 := R.c8g_counts w; have z7 := R.c7g_counts w; have z6 := R.c6w_counts w
  have cb := DiagSq.corrBackZ_counts R w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hdl := w.dst; have hpl := w.pad; have hh := w.hh; have h5 := w.h5
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have r1 := DiagSq.rawClearT_counts R.lo R.dlo R.pad R.carry (by omega) (by omega) hpl (by omega)
  have r2 := DiagSq.rawClearT_counts R.hi R.dhi R.pad R.carry (by omega) (by omega) hpl (by omega)
  have r5 := DiagSq.rawClearT_counts R.S R.T R.pad R.carry (by omega) (by omega) hpl (by omega)
  have da1 := DiagSq.dAddZ_counts R.lo R.dlo R.carry R.cin (by omega) (by omega) (by omega)
  have da2 := DiagSq.dAddZ_counts R.hi R.dhi R.carry R.cin (by omega) (by omega) (by omega)
  simp only [clear,DiagSq.clear,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem makeC_counts_diff (R : KRegs) (w : R.W) :
    toffoliCount (makeC R)+(R.bank.length-R.h)+10=toffoliCount (DiagSq.makeC R) ∧
    measurementCount (makeC R)+4=measurementCount (DiagSq.makeC R) := by
  have a := R.piece_counts w
  have b := R.scl1591_counts w
  have z := DiagSq.makeZ_counts_rel R w
  simp only [makeC,DiagSq.makeC,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem clearC_counts_diff (R : KRegs) (w : R.W) :
    toffoliCount (clearC R)+(R.bank.length-R.h)+10=toffoliCount (DiagSq.clearC R) ∧
    measurementCount (clearC R)+4=measurementCount (DiagSq.clearC R) := by
  have h := clear_counts_diff R w
  simp only [clearC,DiagSq.clearC,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem clear_support (R : KRegs) (w : R.W) : wires (clear R)⊆R.all.toFinset := by
  have old := (DiagSq.steps_support R w).2
  have new := R.scl1591_support w
  have pcs := R.piece_support w
  have q2 := pcs.2.2.2.1
  simp only [wires_append,Finset.union_subset_iff] at q2
  have c8w : wires R.c8g⊆R.all.toFinset := R.c8g_wires.trans q2.1.1
  have c7w : wires R.c7g⊆R.all.toFinset := R.c7g_wires.trans q2.1.2
  have c6w' : wires R.c6w⊆R.all.toFinset := R.c6w_wires.trans q2.2
  clear q2 pcs
  simp only [clear,DiagSq.clear,wires_append,Finset.union_subset_iff] at old ⊢
  have rS : wires (rawClearT R.S R.T R.pad R.carry)⊆R.all.toFinset :=
    (DiagSq.rawClearT_wires_sub _ _ _ _).trans (by tauto)
  have rH : wires (rawClearT R.hi R.dhi R.pad R.carry)⊆R.all.toFinset :=
    (DiagSq.rawClearT_wires_sub _ _ _ _).trans (by tauto)
  have rL : wires (rawClearT R.lo R.dlo R.pad R.carry)⊆R.all.toFinset :=
    (DiagSq.rawClearT_wires_sub _ _ _ _).trans (by tauto)
  have cbw : wires (corrBackZ R)⊆R.all.toFinset := (DiagSq.wires_of_mem (DiagSq.corrBackZ_mem R)).trans (by tauto)
  have daw1 : wires (dAddZ R.lo R.dlo R.carry R.cin)⊆R.all.toFinset := (DiagSq.wires_of_mem (DiagSq.dAddZ_mem _ _ _ _)).trans (by tauto)
  have daw2 : wires (dAddZ R.hi R.dhi R.carry R.cin)⊆R.all.toFinset := (DiagSq.wires_of_mem (DiagSq.dAddZ_mem _ _ _ _)).trans (by tauto)
  tauto

theorem makeC_support (R : KRegs) (w : R.W) : wires (makeC R)⊆R.all.toFinset := by
  simpa only [makeC,wires_append,Finset.union_subset_iff] using
    And.intro (DiagSq.makeZ_support R w) (R.scl1591_support w)

theorem clearC_support (R : KRegs) (w : R.W) : wires (clearC R)⊆R.all.toFinset := by
  simpa only [clearC,wires_append,Finset.union_subset_iff] using
    And.intro (R.piece_support w).1 (clear_support R w)

theorem clear_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (clear R) := by
  have old := (DiagSq.steps_physical R w hn).2
  have new := R.scl1591_physical w hn
  have z8 := R.c8g_physical hn; have z7 := R.c7g_physical hn; have z6 := R.c6w_physical hn
  have oldm := (DiagSq.steps_physical R w hn).1
  simp only [DiagSq.make,DiagSq.headBlock,DiagSq.seeds,gatePhysical_append] at oldm
  simp only [clear,DiagSq.clear,gatePhysical_append] at old ⊢
  have rS := DiagSq.rawClearT_physical_of R.S R.T R.pad R.carry (by tauto) (by tauto)
  have rH := DiagSq.rawClearT_physical_of R.hi R.dhi R.pad R.carry (by tauto) (by tauto)
  have rL := DiagSq.rawClearT_physical_of R.lo R.dlo R.pad R.carry (by tauto) (by tauto)
  have cbp : GatePhysical (corrBackZ R) := fun i hi => (show GatePhysical (corrBack R) by tauto) i (DiagSq.corrBackZ_mem R i hi)
  have dap1 : GatePhysical (dAddZ R.lo R.dlo R.carry R.cin) := fun i hi => (show GatePhysical (mappedDiagAdd R.lo R.dlo R.carry R.cin) by tauto) i (DiagSq.dAddZ_mem _ _ _ _ i hi)
  have dap2 : GatePhysical (dAddZ R.hi R.dhi R.carry R.cin) := fun i hi => (show GatePhysical (mappedDiagAdd R.hi R.dhi R.carry R.cin) by tauto) i (DiagSq.dAddZ_mem _ _ _ _ i hi)
  tauto

theorem makeC_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (makeC R) := by
  simpa only [makeC,gatePhysical_append] using
    And.intro (DiagSq.makeZ_physical R w hn) (R.scl1591_physical w hn)

theorem clearC_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (clearC R) := by
  simpa only [clearC,gatePhysical_append] using
    And.intro (R.piece_physical hn).1 (clear_physical R w hn)

theorem clear_slots_le (R : KRegs) : Challenge.gateSlots (clear R)≤Challenge.gateSlots (DiagSq.clear R) := by
  have h := R.scl1591_slots
  have z8 := R.c8g_slots; have z7 := R.c7g_slots; have z6 := R.c6w_slots
  have rS := DiagSq.rawClearT_slots_le R.S R.T R.pad R.carry
  have rH := DiagSq.rawClearT_slots_le R.hi R.dhi R.pad R.carry
  have rL := DiagSq.rawClearT_slots_le R.lo R.dlo R.pad R.carry
  have cb := DiagSq.corrBackZ_slots R
  have da1 := DiagSq.dAddZ_slots R.lo R.dlo R.carry R.cin; have da2 := DiagSq.dAddZ_slots R.hi R.dhi R.carry R.cin
  simp only [clear,DiagSq.clear,Challenge.gateSlots_append] at *
  omega

theorem makeC_slots_le (R : KRegs) : Challenge.gateSlots (makeC R)≤Challenge.gateSlots (DiagSq.makeC R) := by
  have h := R.scl1591_slots
  have z := DiagSq.makeZ_slots R
  simp only [makeC,DiagSq.makeC,Challenge.gateSlots_append] at *
  omega

theorem clearC_slots_le (R : KRegs) : Challenge.gateSlots (clearC R)≤Challenge.gateSlots (DiagSq.clearC R) := by
  have h := clear_slots_le R
  simp only [clearC,DiagSq.clearC,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.Z5Diagonal

namespace ECDSAAdd.Entrant.Z5Diagonal
open Arithmetic

theorem clear_counts (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (clear R)=DiagSq.cost R-R.h-10 ∧ measurementCount (clear R)+4=DiagSq.cost R := by
  have a := clear_counts_diff R w
  have b := DiagSq.clear_counts R w he
  constructor <;> omega

theorem steps_support (R : KRegs) (w : R.W) :
    wires (DiagSq.makeZ R)⊆R.all.toFinset ∧ wires (clear R)⊆R.all.toFinset :=
  ⟨DiagSq.makeZ_support R w,clear_support R w⟩

theorem steps_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) :
    GatePhysical (DiagSq.makeZ R) ∧ GatePhysical (clear R) :=
  ⟨DiagSq.makeZ_physical R w hn,clear_physical R w hn⟩

theorem tiny_slots (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h≤33) :
    Challenge.gateSlots (DiagSq.makeZ R)≤150800 ∧ Challenge.gateSlots (clear R)≤150800 :=
  ⟨(DiagSq.makeZ_slots R).trans (DiagSq.tiny_slots R w he hh).1,(clear_slots_le R).trans (DiagSq.tiny_slots R w he hh).2⟩

end ECDSAAdd.Entrant.Z5Diagonal
end

section
namespace ECDSAAdd.Entrant.TrimSquare3
open Arithmetic
theorem tsq3_slots_rel (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (tsq3 xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsq2 xs dst pad carry cin) ∧
    Challenge.gateSlots (tsqc3 xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsqc2 xs dst pad carry cin) := by
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact ⟨le_refl _,le_refl _⟩
  · rw [e1,e2,e3,e4]
    have d := addDrop_slots x y cy c
    simp only [Challenge.gateSlots_append]
    constructor <;> omega
end ECDSAAdd.Entrant.TrimSquare3

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic
theorem sq_plain3_make (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqMake xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimSquare3.tsq3 xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimSquare3.tsq3_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,trivial,fun q h _ => r.2.2 q h⟩
theorem sq_plain3_clear (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqClear xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimSquare3.tsqc3 xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimSquare3.tsqc3_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,rfl,fun q h _ => r.2.2 q h⟩
end ECDSAAdd.Entrant.LowZero18LowK

end

-- ===== ECDSAAdd.Submission.Entrant.LowZero18Core =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18KRegs
-- consolidated import: import ECDSAAdd.Submission.Entrant.FrontierSumCleanup1591LowK

/-! LowZero changes only the final inner addition and four outer additions.
The old raw leaves and the checked675 sum cleanup remain in use. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.LowZero18Diagonal
open Arithmetic DiagSq

def make (R : KRegs) : Program := DiagSq.makeZ R
def makeC (R : KRegs) : Program := make R++R.scl1591
abbrev clear := Z5Diagonal.clear
abbrev clearC := Z5Diagonal.clearC

theorem make_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (make R) m s).phase=s.phase ∧
    regValue R.dst (run (make R) m s).basis=(regValue R.bank s.basis)^2 ∧
    regValue R.S (run (make R) m s).basis=regValue R.lo s.basis+regValue R.hi s.basis ∧
    regValue R.T (run (make R) m s).basis=2*regValue R.lo s.basis*regValue R.hi s.basis ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (make R) m s).basis q=s.basis q :=
  DiagSq.makeZ_correct R w he hh hn s m hd0 hS0 hT0 hz0 hp0 hc0 hi0

variable (R : KRegs)

theorem diag_sq_full_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (make R) R.invF := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  have r := make_correct R w he hh hn s m hd0 (KRegs.xz hX (fun q h => List.mem_append_left _ h))
    (KRegs.xz hX (fun q h => List.mem_append_right _ h)) (KRegs.xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [KRegs.invF,r.2.2.1,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  exact ⟨rfl,rfl⟩
theorem diag_sq_cl_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (makeC R) R.invC := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  let a := m.take (measurementCount (make R))
  let b := m.drop (measurementCount (make R))
  have r := make_correct R w he hh hn s a hd0 (KRegs.xz hX (fun q h => List.mem_append_left _ h))
    (KRegs.xz hX (fun q h => List.mem_append_right _ h)) (KRegs.xz hz0 hz) hp0 hc0 hi0
  generalize hu : run (make R) a s=u at r
  have fu : ∀q,q∉R.S → q∉R.T → q∉R.dst → u.basis q=s.basis q := fun q a b c => r.2.2.2.2 q c a b
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S ∧ q∉R.T ∧ q∉R.dst) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => fu q (hl q hq).1 (hl q hq).2.1 (hl q hq).2.2)
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin) : q∉R.S ∧ q∉R.T ∧ q∉R.dst :=
    let x := R.outside hn q h; ⟨x.2.1,x.2.2,x.1⟩
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := R.scl1591_correct w hn u b (by rw [r.2.2.1,lo,hi])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (KRegs.xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((fu _ (o _ (by simp)).1 (o _ (by simp)).2.1 (o _ (by simp)).2.2).trans hi0)
  have eq : run (makeC R) m s=run R.scl1591 b u := by
    rw [makeC,run_append,←hu]
  rw [eq]
  have sT := R.outside hn
  have dS : ∀q∈R.dst,q∉R.S := kdis hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have TS : ∀q∈R.T,q∉R.S := kdis hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  refine ⟨c.1.trans r.1,?_,?_,?_⟩
  · rw [kkeep c.2.2 dS,r.2.1]
  · refine ⟨c.2.1,?_⟩
    rw [kkeep c.2.2 TS,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2 q xS).trans (fu q xS xT h)

abbrev diag_sq_full_clear := Z5Diagonal.diag_sq_full_clear
abbrev diag_sq_cl_clear := Z5Diagonal.diag_sq_cl_clear

attribute [local irreducible] toffoliCount measurementCount Challenge.gateSlots

theorem make_counts_diff (w : R.W) :
    toffoliCount (make R)+10=toffoliCount (DiagSq.make R) ∧
    measurementCount (make R)+4=measurementCount (DiagSq.make R) :=
  DiagSq.makeZ_counts_rel R w

theorem make_counts (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (make R)=DiagSq.cost R-10 ∧ measurementCount (make R)=DiagSq.cost R-4 := by
  have a := DiagSq.makeZ_counts R w he
  unfold make
  constructor <;> omega

theorem make_support_subset (w : R.W) : wires (make R)⊆wires (DiagSq.make R) := by
  have a := R.m6w_wires; have b := R.m7g_wires; have c := R.m8g_wires
  have d := seedsT_wires R
  have e := wires_of_mem (corrZ_mem R)
  have f1 := wires_of_mem (dSubZ_mem R.lo R.dlo R.carry R.cin)
  have f2 := wires_of_mem (dSubZ_mem R.hi R.dhi R.carry R.cin)
  simp only [make,DiagSq.makeZ,DiagSq.make,headBlockZ,headBlock,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union d (Finset.union_subset_union
    (Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union a b) e) f1) f2)) c

theorem makeC_support_subset (w : R.W) :
    wires (makeC R)⊆wires (FrontierSumCleanup1591Diagonal.makeC R) := by
  simp only [makeC,FrontierSumCleanup1591Diagonal.makeC,wires_append]
  exact Finset.union_subset_union (make_support_subset R w) (Finset.Subset.refl _)

theorem make_support (w : R.W) : wires (make R)⊆R.all.toFinset :=
  (make_support_subset R w).trans (DiagSq.steps_support R w).1

theorem makeC_support (w : R.W) : wires (makeC R)⊆R.all.toFinset :=
  (makeC_support_subset R w).trans (FrontierSumCleanup1591Diagonal.makeC_support R w)

theorem clear_support_subset : wires (clear R)⊆wires (FrontierSumCleanup1591Diagonal.clear R) := by
  have z8 := R.c8g_wires; have z7 := R.c7g_wires; have z6 := R.c6w_wires
  simp only [clear,Z5Diagonal.clear,FrontierSumCleanup1591Diagonal.clear,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact z8 | exact z7 | exact z6 | exact wires_of_mem (dAddZ_mem _ _ _ _) |
    exact wires_of_mem (corrBackZ_mem R) | exact rawClearT_wires_sub _ _ _ _ | exact Finset.Subset.refl _

theorem clearC_support_subset : wires (clearC R)⊆wires (FrontierSumCleanup1591Diagonal.clearC R) := by
  simp only [clearC,Z5Diagonal.clearC,FrontierSumCleanup1591Diagonal.clearC,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (clear_support_subset R)

theorem clear_slots_old : Challenge.gateSlots (clear R)≤Challenge.gateSlots (FrontierSumCleanup1591Diagonal.clear R) := by
  have z8 := R.c8g_slots; have z7 := R.c7g_slots; have z6 := R.c6w_slots
  have rS := DiagSq.rawClearT_slots_le R.S R.T R.pad R.carry
  have rH := DiagSq.rawClearT_slots_le R.hi R.dhi R.pad R.carry
  have rL := DiagSq.rawClearT_slots_le R.lo R.dlo R.pad R.carry
  have cb := DiagSq.corrBackZ_slots R
  have da1 := DiagSq.dAddZ_slots R.lo R.dlo R.carry R.cin
  have da2 := DiagSq.dAddZ_slots R.hi R.dhi R.carry R.cin
  simp only [clear,Z5Diagonal.clear,FrontierSumCleanup1591Diagonal.clear,Challenge.gateSlots_append] at *
  omega

theorem clearC_slots_old : Challenge.gateSlots (clearC R)≤Challenge.gateSlots (FrontierSumCleanup1591Diagonal.clearC R) := by
  have h := clear_slots_old R
  simp only [clear,clearC,Z5Diagonal.clearC,FrontierSumCleanup1591Diagonal.clearC,Challenge.gateSlots_append] at *
  omega

abbrev clear_counts := Z5Diagonal.clear_counts
abbrev clear_support := Z5Diagonal.clear_support
abbrev clearC_support := Z5Diagonal.clearC_support
abbrev clear_physical := Z5Diagonal.clear_physical
abbrev clearC_physical := Z5Diagonal.clearC_physical
abbrev clear_slots_le := Z5Diagonal.clear_slots_le
abbrev clearC_slots_le := Z5Diagonal.clearC_slots_le

theorem steps_support (w : R.W) :
    wires (make R)⊆R.all.toFinset ∧ wires (clear R)⊆R.all.toFinset :=
  ⟨make_support R w,clear_support R w⟩

theorem make_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical (make R) :=
  DiagSq.makeZ_physical R w hn

theorem makeC_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical (makeC R) :=
  (gatePhysical_append _ _).mpr ⟨make_physical R w hn,R.scl1591_physical w hn⟩

theorem steps_physical (w : R.W) (hn : R.all.Nodup) :
    GatePhysical (make R) ∧ GatePhysical (clear R) :=
  ⟨make_physical R w hn,clear_physical R w hn⟩

theorem make_slots_le (w : R.W) :
    Challenge.gateSlots (make R)≤Challenge.gateSlots (DiagSq.make R) :=
  DiagSq.makeZ_slots R

theorem makeC_slots_old (w : R.W) :
    Challenge.gateSlots (makeC R)≤Challenge.gateSlots (FrontierSumCleanup1591Diagonal.makeC R) := by
  have z := make_slots_le R w
  simp only [makeC,FrontierSumCleanup1591Diagonal.makeC,Challenge.gateSlots_append]
  omega

theorem makeC_slots_le (w : R.W) :
    Challenge.gateSlots (makeC R)≤Challenge.gateSlots (DiagSq.makeC R) :=
  (makeC_slots_old R w).trans (FrontierSumCleanup1591Diagonal.makeC_slots_le R)

theorem tiny_slots (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h≤33) :
    Challenge.gateSlots (make R)≤150800 ∧ Challenge.gateSlots (clear R)≤150800 :=
  ⟨(make_slots_le R w).trans (DiagSq.tiny_slots R w he hh).1,
    (Z5Diagonal.tiny_slots R w he hh).2⟩

end ECDSAAdd.Entrant.LowZero18Diagonal

namespace ECDSAAdd.Entrant.LowZero18KG
open Arithmetic KG
variable (K : KG)
def make : Program := K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7y++K.R.m8z++K.R.scl1591
def clear : Program := K.R.smk++K.R.c8z++K.R.c7y++K.R.c6++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c
theorem make_correct (sp : K.Spec) (hn : K.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=0) (hS0 : regValue K.R.S s.basis=0)
    (hT0 : regValue K.R.T s.basis=0) (hX0 : regValue K.X s.basis=0)
    (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    (run (make K) m s).phase=s.phase ∧
    regValue K.R.dst (run (make K) m s).basis=(regValue K.R.bank s.basis)^2 ∧
    regValue K.R.S (run (make K) m s).basis=0 ∧
    regValue K.R.T (run (make K) m s).basis=2*regValue K.R.lo s.basis*regValue K.R.hi s.basis ∧
    K.I1 (regValue K.R.lo s.basis) (run (make K) m s).basis ∧
    K.I2 (regValue K.R.hi s.basis) (run (make K) m s).basis ∧
    K.I5 (regValue K.R.lo s.basis+regValue K.R.hi s.basis) (run (make K) m s).basis ∧
    ∀q,q∉K.R.dst → q∉K.R.T → q∉K.X → (run (make K) m s).basis q=s.basis q := by
  have w := sp.w
  have hR := K.rnd hn
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := K.R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  have bv := K.R.bank_value w s.basis
  rw [bv]
  generalize ha : regValue K.R.lo s.basis=a
  generalize hb : regValue K.R.hi s.basis=b
  have aLt : a<2^K.R.h := by rw [←ha,←L0]; exact regValue_lt _ _
  have bLt : b<2^(K.R.bank.length-K.R.h) := by rw [←hb,←L1]; exact regValue_lt _ _
  have mt {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.take k) : q∈l := List.mem_of_mem_take h
  have md {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.drop k) : q∈l := List.mem_of_mem_drop h
  have x1 {q : Wire} (h : q∈K.X1) : q∈K.X := by simp [X,h]
  have x2 {q : Wire} (h : q∈K.X2) : q∈K.X := by simp [X,h]
  have x5 {q : Wire} (h : q∈K.X5) : q∈K.X := by simp [X,h]
  have xo (q : Wire) (h : q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) : q∉K.X := by
    apply K.rX hn q; simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
  have outV (t : State) (G : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t.basis q=s.basis q) (r : List Wire)
      (hr : ∀q∈r,q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) :
      regValue r t.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => let o := K.R.outside hR q (hr q hq); G q o.1 o.2.1 o.2.2 (xo q (hr q hq)))
  have zero (r : List Wire) (big : List Wire) (hz : regValue big s.basis=0) (sub : ∀q∈r,q∈big) :
      regValue r s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (sub q hq))
  have nD : K.R.dst.Nodup := knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have cinO : K.R.cin∉K.R.dst ∧ K.R.cin∉K.R.S ∧ K.R.cin∉K.R.T := K.R.outside hR K.R.cin (by simp)
  have cinX : K.R.cin∉K.X := xo _ (by simp)
  obtain ⟨a7,r8,e8⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7y++K.R.m8z) K.R.scl1591 m s
  obtain ⟨a6,r7,e7⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7y) K.R.m8z a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6) K.R.m7y a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5) K.R.m6 a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (K.Q1++K.Q2++K.R.smk) K.Q5 a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (K.Q1++K.Q2) K.R.smk a3 s
  obtain ⟨r1,r2,e2⟩ := kseq K.Q1 K.Q2 a2 s
  rw [show (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7y++K.R.m8z++K.R.scl1591 from rfl,e8,e7,e6,e5,e4,e3,e2]
  -- Q1: a^2 into dlo
  have st1 := sp.mk1 s r1 (zero _ _ hd0 (fun q h => mt h)) (zero _ _ hX0 (fun q h => x1 h)) hp0 hc0 hz0 hi0
  rw [ha] at st1
  generalize run K.Q1 r1 s=s1 at st1 ⊢
  have G1 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s1.basis q=s.basis q :=
    fun q h _ _ x => st1.2.2.2 q (fun y => h (mt y)) (fun y => x (x1 y))
  -- Q2: b^2 into dhi
  have dhi1 : regValue K.R.dhi s1.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hd0 (fun q h => md h))
  have X21 : regValue K.X2 s1.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hX0 (fun q h => x2 h))
  have hi1 : regValue K.R.hi s1.basis=b := (outV s1 G1 _ (fun q h => Or.inl (md h))).trans hb
  have st2 := sp.mk2 s1 r2 dhi1 X21 ((outV s1 G1 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV s1 G1 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV s1 G1 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  rw [hi1] at st2
  generalize run K.Q2 r2 s1=s2 at st2 ⊢
  have F2 : ∀q,q∉K.R.dhi → q∉K.X2 → s2.basis q=s1.basis q := st2.2.2.2
  have G2 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s2.basis q=s.basis q :=
    fun q h hS hT x => (F2 q (fun y => h (md y)) (fun y => x (x2 y))).trans (G1 q h hS hT x)
  have dlo2 : regValue K.R.dlo s2.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st1.2.1
  have I12 : K.I1 a s2.basis := sp.lc1 a s1.basis s2.basis (fun q hq => (F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st1.2.2.1
  -- sum register
  have S2 : regValue K.R.S s2.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    (F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).trans (st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)))).trans hS0
  have st3 := K.R.smk_correct w hR s2 r3 S2 ((outV s2 G2 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV s2 G2 K.R.carry (by intro q h; simp [h])).trans hc0) ((G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  have lo2 : regValue K.R.lo s2.basis=a := (outV s2 G2 K.R.lo (fun q h => Or.inl (mt h))).trans ha
  have hi2 : regValue K.R.hi s2.basis=b := (outV s2 G2 K.R.hi (fun q h => Or.inl (md h))).trans hb
  rw [lo2,hi2] at st3
  generalize run K.R.smk r3 s2=s3 at st3 ⊢
  have F3 := st3.2.2
  have G3 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s3.basis q=s.basis q :=
    fun q h hS hT x => (F3 q hS).trans (G2 q h hS hT x)
  have dlo3 : regValue K.R.dlo s3.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo2
  have dhi3 : regValue K.R.dhi s3.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st2.2.1
  have I13 : K.I1 a s3.basis := sp.lc1 a s2.basis s3.basis (fun q hq => (F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I12
  have I23 : K.I2 b s3.basis := sp.lc2 b s2.basis s3.basis (fun q hq => (F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st2.2.2.1
  -- Q5: T = (a+b)^2
  have back3 (q : Wire) (h1 : q∉K.R.dlo) (h2 : q∉K.X1) (h3 : q∉K.R.dhi) (h4 : q∉K.X2) (h5 : q∉K.R.S) :
      s3.basis q=s.basis q :=
    (F3 q h5).trans ((F2 q h3 h4).trans (st1.2.2.2 q h1 h2))
  have T3 : regValue K.R.T s3.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    back3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hT0
  have X53 : regValue K.X5 s3.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    back3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hX0 (fun q h => x5 h))
  have st5 := sp.mk5 s3 r4 T3 X53 ((outV s3 G3 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV s3 G3 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV s3 G3 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  rw [st3.2.1] at st5
  generalize run K.Q5 r4 s3=s5 at st5 ⊢
  have F5 : ∀q,q∉K.R.T → q∉K.X5 → s5.basis q=s3.basis q := st5.2.2.2
  have G5 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s5.basis q=s.basis q :=
    fun q h hS hT x => (F5 q hT (fun y => x (x5 y))).trans (G3 q h hS hT x)
  have dlo5 : regValue K.R.dlo s5.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo3
  have dhi5 : regValue K.R.dhi s5.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi3
  have S5 : regValue K.R.S s5.basis=a+b := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st3.2.1
  have I15 : K.I1 a s5.basis := sp.lc1 a s3.basis s5.basis (fun q hq => (F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I13
  have I25 : K.I2 b s5.basis := sp.lc2 b s3.basis s5.basis (fun q hq => (F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I23
  have sumLt : a+b<2^K.R.S.length := by
    have hp : 2^K.R.h≤2^(K.R.bank.length-K.R.h) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq : 2^K.R.S.length=2*2^(K.R.bank.length-K.R.h) := by rw [hSl,pow_succ]; ring
    omega
  have sqLt : (a+b)^2<2^K.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  -- T -= a^2
  have st6 : (run K.R.m6 r5 s5).phase=s5.phase ∧ regValue K.R.T (run K.R.m6 r5 s5).basis=2*a*b+b^2 ∧
      ∀q,q∉K.R.T → (run K.R.m6 r5 s5).basis q=s5.basis q := by
    unfold KRegs.m6
    obtain ⟨p,f,v⟩ := BalancedInverse.subInPlace_any_correct (K.R.dlo++K.R.zA) K.R.T
      (K.R.carry.take (K.R.T.length-1)) K.R.cin (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega)
      (by simp only [List.length_take]; omega) s5 r5
      (fun q hq => (regValue_zero _ _).mp ((outV s5 G5 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dlo5,outV s5 G5 K.R.zA (by intro q h; simp [mt h]),zero K.R.zA K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.T.length-2*K.R.h) from h)),
      st5.2.1,G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [ex]; omega) sqLt,ex]; omega
  generalize run K.R.m6 r5 s5=s6 at st6 ⊢
  have G6 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s6.basis q=s.basis q :=
    fun q h hS hT x => (st6.2.2 q hT).trans (G5 q h hS hT x)
  have dlo6 : regValue K.R.dlo s6.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo5
  have dhi6 : regValue K.R.dhi s6.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi5
  -- T -= b^2
  have st7 : (run K.R.m7y r6 s6).phase=s6.phase ∧ regValue K.R.T (run K.R.m7y r6 s6).basis=2*a*b ∧
      ∀q,q∉K.R.T → (run K.R.m7y r6 s6).basis q=s6.basis q := by
    obtain ⟨p,f,v⟩ := K.R.m7y_correct w hR s6 r6
      (fun q hq => (regValue_zero _ _).mp ((outV s6 G6 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by
        have hT := LowZero.head_bit K.R.T [] s6.basis (K.R.T_ne w)
        rw [List.append_nil] at hT
        rw [LowZero.head_bit K.R.dhi K.R.zB s6.basis (K.R.dhi_ne w),hT,dhi6,st6.2.1,
          show 2*a*b+b^2=b^2+2*(a*b) by ring,Nat.add_mul_mod_self_left]
        cases decide (b^2%2=1) <;> rfl)
      ((G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
      (by rw [ECDSAAdd.Entrant.KRegs.bit1 K.R.dhi K.R.zB s6.basis (K.R.dhi_two w),dhi6,ECDSAAdd.Entrant.KRegs.sq_bit1]; rfl)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dhi6,outV s6 G6 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h)),
      st6.2.1,G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by omega) (by rw [ex] at sqLt; omega)]; omega
  generalize run K.R.m7y r6 s6=s7 at st7 ⊢
  have G7 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s7.basis q=s.basis q :=
    fun q h hS hT x => (st7.2.2 q hT).trans (G6 q h hS hT x)
  have dlo7 : regValue K.R.dlo s7.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st7.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo6
  have dhi7 : regValue K.R.dhi s7.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st7.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi6
  have D7 : regValue K.R.dst s7.basis=a^2+2^(2*K.R.h)*b^2 := by rw [K.R.dst_value w,dlo7,dhi7]
  -- dst += 2^h * 2ab
  have st8 : (run K.R.m8z r7 s7).phase=s7.phase ∧
      regValue K.R.dmid (run K.R.m8z r7 s7).basis=(2*a*b+(a^2+2^(2*K.R.h)*b^2)/2^K.R.h)%2^(2*K.R.bank.length-K.R.h) ∧
      ∀q,q∉K.R.dmid → (run K.R.m8z r7 s7).basis q=s7.basis q := by
    obtain ⟨p,f,v⟩ := K.R.m8z_correct w hR s7 r7 (a*b)
      (fun q hq => (regValue_zero _ _).mp ((outV s7 G7 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by rw [st7.2.1]; ring) ((G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,st7.2.1,outV s7 G7 K.R.zM (by intro q h; simp [mt h]),zero K.R.zM K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.dmid.length-K.R.T.length) from h)),
      show regValue K.R.dmid s7.basis=regValue K.R.dst s7.basis/2^K.R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst K.R.h (by omega) s7.basis,D7,
      G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0,L4]
    simp
  generalize run K.R.m8z r7 s7=s8 at st8 ⊢
  have G8 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s8.basis q=s.basis q :=
    fun q h hS hT x => (st8.2.2 q (fun y => h (md y))).trans (G7 q h hS hT x)
  have D8 : regValue K.R.dst s8.basis=(a+2^K.R.h*b)^2 := by
    rw [K.R.dst_value_mid w,st8.2.1,kkeep st8.2.2 (by
      intro q hq hx
      have c1 := List.count_pos_iff.mpr hq; have c2 := List.count_pos_iff.mpr hx
      have c3 := (K.R.counts q).2.2.1
      have c4 := List.nodup_iff_count_le_one.mp nD q
      omega),CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst K.R.h (by omega),D7]
    exact KRegs.kfinal a b K.R.h K.R.bank.length aLt bLt (by omega)
  -- facts between s5 and s8: only T and dmid changed
  have back8 (q : Wire) (hT : q∉K.R.T) (hd : q∉K.R.dst) : s8.basis q=s5.basis q :=
    (st8.2.2 q (fun y => hd (md y))).trans ((st7.2.2 q hT).trans (st6.2.2 q hT))
  have S8 : regValue K.R.S s8.basis=a+b := (regValue_congr _ _ _ (fun q hq => back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S5
  have T8 : regValue K.R.T s8.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st8.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.1
  have I18 : K.I1 a s8.basis := sp.lc1 a s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I15
  have I28 : K.I2 b s8.basis := sp.lc2 b s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I25
  have I58 : K.I5 (a+b) s8.basis := sp.lc5 (a+b) s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st5.2.2.1
  -- clean the sum register
  have st9 := K.R.scl1591_correct w hR s8 r8
    (by rw [S8,(outV s8 G8 K.R.lo (fun q h => Or.inl (mt h))).trans ha,(outV s8 G8 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    ((outV s8 G8 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV s8 G8 K.R.carry (by intro q h; simp [h])).trans hc0) ((G8 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.R.scl1591 r8 s8=s9 at st9 ⊢
  refine ⟨st9.1.trans (st8.1.trans (st7.1.trans (st6.1.trans (st5.1.trans (st3.1.trans
    (st2.1.trans st1.1)))))),?_,st9.2.1,?_,?_,?_,?_,?_⟩
  · rw [←D8]; exact regValue_congr _ _ _ (fun q hq => st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))
  · rw [←T8]; exact regValue_congr _ _ _ (fun q hq => st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))
  · exact sp.lc1 a s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I18
  · exact sp.lc2 b s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I28
  · exact sp.lc5 (a+b) s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I58
  · intro q hd hT hx
    by_cases hS : q∈K.R.S
    · exact ((regValue_zero _ _).mp st9.2.1 q hS).trans ((regValue_zero _ _).mp hS0 q hS).symm
    · exact (st9.2.2 q hS).trans (G8 q hd hS hT hx)

theorem clear_correct (sp : K.Spec) (hn : K.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=(regValue K.R.bank s.basis)^2) (hS0 : regValue K.R.S s.basis=0)
    (hT0 : regValue K.R.T s.basis=2*regValue K.R.lo s.basis*regValue K.R.hi s.basis)
    (hI1 : K.I1 (regValue K.R.lo s.basis) s.basis) (hI2 : K.I2 (regValue K.R.hi s.basis) s.basis)
    (hI5 : K.I5 (regValue K.R.lo s.basis+regValue K.R.hi s.basis) s.basis)
    (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    (run (clear K) m s).phase=s.phase ∧
    regValue K.R.dst (run (clear K) m s).basis=0 ∧
    regValue K.R.S (run (clear K) m s).basis=0 ∧
    regValue K.R.T (run (clear K) m s).basis=0 ∧
    regValue K.X (run (clear K) m s).basis=0 ∧
    ∀q,q∉K.R.dst → q∉K.R.T → q∉K.X → (run (clear K) m s).basis q=s.basis q := by
  have w := sp.w
  have hR := K.rnd hn
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := K.R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  rw [K.R.bank_value w s.basis] at hd0
  generalize ha : regValue K.R.lo s.basis=a at hd0 hT0 hI1 hI5
  generalize hb : regValue K.R.hi s.basis=b at hd0 hT0 hI2 hI5
  have aLt : a<2^K.R.h := by rw [←ha,←L0]; exact regValue_lt _ _
  have bLt : b<2^(K.R.bank.length-K.R.h) := by rw [←hb,←L1]; exact regValue_lt _ _
  have mt {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.take k) : q∈l := List.mem_of_mem_take h
  have md {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.drop k) : q∈l := List.mem_of_mem_drop h
  have x1 {q : Wire} (h : q∈K.X1) : q∈K.X := by simp [X,h]
  have x2 {q : Wire} (h : q∈K.X2) : q∈K.X := by simp [X,h]
  have x5 {q : Wire} (h : q∈K.X5) : q∈K.X := by simp [X,h]
  have xo (q : Wire) (h : q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) : q∉K.X := by
    apply K.rX hn q; simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
  have outV (t : State) (G : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t.basis q=s.basis q) (r : List Wire)
      (hr : ∀q∈r,q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) :
      regValue r t.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => let o := K.R.outside hR q (hr q hq); G q o.1 o.2.1 o.2.2 (xo q (hr q hq)))
  have zero (r : List Wire) (big : List Wire) (hz : regValue big s.basis=0) (sub : ∀q∈r,q∈big) :
      regValue r s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (sub q hq))
  have nD : K.R.dst.Nodup := knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have cinO : K.R.cin∉K.R.dst ∧ K.R.cin∉K.R.S ∧ K.R.cin∉K.R.T := K.R.outside hR K.R.cin (by simp)
  have cinX : K.R.cin∉K.X := xo _ (by simp)
  have hp2 : 2^K.R.h≤2^(K.R.bank.length-K.R.h) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq2 : 2^K.R.S.length=2*2^(K.R.bank.length-K.R.h) := by rw [hSl,pow_succ]; ring
  have sumLt : a+b<2^K.R.S.length := by omega
  have sqLt : (a+b)^2<2^K.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  have hX : (a+2^K.R.h*b)^2=(a^2+2^(2*K.R.h)*b^2)+2^K.R.h*(2*a*b) := by ring
  have hpos : 0<2^K.R.h := Nat.two_pow_pos _
  have XLt : (a+2^K.R.h*b)^2<2^(2*K.R.bank.length) := by
    have hsplit : 2^K.R.bank.length=2^K.R.h*2^(K.R.bank.length-K.R.h) := by rw [←pow_add]; congr 1; omega
    have hm := Nat.mul_le_mul_left (2^K.R.h) (show b+1≤2^(K.R.bank.length-K.R.h) by omega)
    rw [Nat.mul_add,Nat.mul_one,←hsplit] at hm
    exact square_bound _ _ (by omega)
  have aSq : a^2<2^(2*K.R.h) := square_bound _ _ aLt
  obtain ⟨a7,r8,e8⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7y++K.R.c6++K.Q5c++K.R.scl1591++K.Q2c) K.Q1c m s
  obtain ⟨a6,r7,e7⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7y++K.R.c6++K.Q5c++K.R.scl1591) K.Q2c a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7y++K.R.c6++K.Q5c) K.R.scl1591 a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7y++K.R.c6) K.Q5c a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7y) K.R.c6 a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (K.R.smk++K.R.c8z) K.R.c7y a3 s
  obtain ⟨r1,r2,e2⟩ := kseq K.R.smk K.R.c8z a2 s
  rw [show (clear K)=K.R.smk++K.R.c8z++K.R.c7y++K.R.c6++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c from rfl,e8,e7,e6,e5,e4,e3,e2]
  -- rebuild S
  have st1 := K.R.smk_correct w hR s r1 hS0 hz0 hc0 hi0
  rw [ha,hb] at st1
  generalize run K.R.smk r1 s=t1 at st1 ⊢
  have G1 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t1.basis q=s.basis q := fun q _ h _ _ => st1.2.2 q h
  have T1 : regValue K.R.T t1.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st1.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hT0
  have D1 : regValue K.R.dst t1.basis=(a+2^K.R.h*b)^2 := (regValue_congr _ _ _ (fun q hq => st1.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hd0
  -- dst -= 2^h * 2ab
  have st2 : (run K.R.c8z r2 t1).phase=t1.phase ∧
      regValue K.R.dst (run K.R.c8z r2 t1).basis=a^2+2^(2*K.R.h)*b^2 ∧
      ∀q,q∉K.R.dmid → (run K.R.c8z r2 t1).basis q=t1.basis q := by
    obtain ⟨p,f,v⟩ := K.R.c8z_correct w hR t1 r2
      (fun q hq => (regValue_zero _ _).mp ((outV t1 G1 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by rw [LowZero.head_false_of_even K.R.T K.R.zM t1.basis (a*b) (by rw [T1]; ring) (K.R.T_ne w)]; rfl)
      ((G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
    refine ⟨p,?_,f⟩
    rw [K.R.dst_value_mid w,v,kkeep f (by
      intro q hq hx
      have c1 := List.count_pos_iff.mpr hq; have c2 := List.count_pos_iff.mpr hx
      have c3 := (K.R.counts q).2.2.1
      have c4 := List.nodup_iff_count_le_one.mp nD q
      omega),regValue_append,T1,outV t1 G1 K.R.zM (by intro q h; simp [mt h]),zero K.R.zM K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.dmid.length-K.R.T.length) from h)),
      G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0,
      CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst K.R.h (by omega),
      show regValue K.R.dmid t1.basis=regValue K.R.dst t1.basis/2^K.R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst K.R.h (by omega) t1.basis,D1,L4]
    have hdiv : (a+2^K.R.h*b)^2/2^K.R.h=(a^2+2^(2*K.R.h)*b^2)/2^K.R.h+2*a*b := by
      rw [hX,Nat.add_mul_div_left _ _ hpos]
    have hmod : (a+2^K.R.h*b)^2%2^K.R.h=(a^2+2^(2*K.R.h)*b^2)%2^K.R.h := by
      rw [hX,Nat.add_mul_mod_self_left]
    have hq : (a+2^K.R.h*b)^2/2^K.R.h<2^(2*K.R.bank.length-K.R.h) := by
      rw [Nat.div_lt_iff_lt_mul hpos,←pow_add,show 2*K.R.bank.length-K.R.h+K.R.h=2*K.R.bank.length by omega]
      exact XLt
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod ((a+2^K.R.h*b)^2/2^K.R.h) (2*a*b) _ (by rw [hdiv]; exact Nat.le_add_left _ _) hq,hdiv,hmod,Nat.add_sub_cancel,Nat.mod_add_div]
  generalize run K.R.c8z r2 t1=t2 at st2 ⊢
  have G2 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t2.basis q=s.basis q :=
    fun q h hS hT x => (st2.2.2 q (fun y => h (md y))).trans (G1 q h hS hT x)
  have dlo2 : regValue K.R.dlo t2.basis=a^2 := by
    rw [show regValue K.R.dlo t2.basis=regValue K.R.dst t2.basis%2^(2*K.R.h) from
      CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst (2*K.R.h) (by omega) t2.basis,st2.2.1,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt aSq]
  have dhi2 : regValue K.R.dhi t2.basis=b^2 := by
    rw [show regValue K.R.dhi t2.basis=regValue K.R.dst t2.basis/2^(2*K.R.h) from
      CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst (2*K.R.h) (by omega) t2.basis,st2.2.1,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt aSq,Nat.zero_add]
  have S2 : regValue K.R.S t2.basis=a+b := (regValue_congr _ _ _ (fun q hq => st2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st1.2.1
  have T2 : regValue K.R.T t2.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans T1
  -- T += b^2
  have st3 : (run K.R.c7y r3 t2).phase=t2.phase ∧ regValue K.R.T (run K.R.c7y r3 t2).basis=2*a*b+b^2 ∧
      ∀q,q∉K.R.T → (run K.R.c7y r3 t2).basis q=t2.basis q := by
    obtain ⟨p,f,v⟩ := K.R.c7y_correct w hR t2 r3
      (fun q hq => (regValue_zero _ _).mp ((outV t2 G2 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by
        have hT := LowZero.head_false_of_even K.R.T [] t2.basis (a*b) (by rw [T2]; ring) (K.R.T_ne w)
        rw [List.append_nil] at hT
        rw [hT]; exact Bool.and_false _)
      ((G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
      (by rw [ECDSAAdd.Entrant.KRegs.bit1 K.R.dhi K.R.zB t2.basis (K.R.dhi_two w),dhi2,ECDSAAdd.Entrant.KRegs.sq_bit1]; rfl)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dhi2,outV t2 G2 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h)),
      T2,G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by rw [ex] at sqLt; omega)]; ring
  generalize run K.R.c7y r3 t2=t3 at st3 ⊢
  have G3 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t3.basis q=s.basis q :=
    fun q h hS hT x => (st3.2.2 q hT).trans (G2 q h hS hT x)
  have dlo3 : regValue K.R.dlo t3.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo2
  have dhi3 : regValue K.R.dhi t3.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi2
  have S3 : regValue K.R.S t3.basis=a+b := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S2
  -- T += a^2
  have st4 : (run K.R.c6 r4 t3).phase=t3.phase ∧ regValue K.R.T (run K.R.c6 r4 t3).basis=(a+b)^2 ∧
      ∀q,q∉K.R.T → (run K.R.c6 r4 t3).basis q=t3.basis q := by
    unfold KRegs.c6
    obtain ⟨p,f,v⟩ := addInPlace_correct (K.R.dlo++K.R.zA) K.R.T (K.R.carry.take (K.R.T.length-1)) K.R.cin
      (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t3 r4
      (fun q hq => (regValue_zero _ _).mp ((outV t3 G3 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dlo3,outV t3 G3 K.R.zA (by intro q h; simp [mt h]),zero K.R.zA K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.T.length-2*K.R.h) from h)),
      st3.2.1,G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by rw [ex] at sqLt; omega),ex]; ring
  generalize run K.R.c6 r4 t3=t4 at st4 ⊢
  have G4 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t4.basis q=s.basis q :=
    fun q h hS hT x => (st4.2.2 q hT).trans (G3 q h hS hT x)
  have dlo4 : regValue K.R.dlo t4.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo3
  have dhi4 : regValue K.R.dhi t4.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi3
  have S4 : regValue K.R.S t4.basis=a+b := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S3
  have back4 (q : Wire) (h1 : q∉K.R.S) (h2 : q∉K.R.dst) (h3 : q∉K.R.T) : t4.basis q=s.basis q :=
    (st4.2.2 q h3).trans ((st3.2.2 q h3).trans ((st2.2.2 q (fun y => h2 (md y))).trans (st1.2.2 q h1)))
  -- clear T with the S-square cleanup
  have st5 := sp.cl5 t4 r5 (by rw [st4.2.1,S4])
    (by rw [S4]; exact sp.lc5 (a+b) s.basis t4.basis (fun q hq => (back4 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) hI5)
    ((outV t4 G4 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t4 G4 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t4 G4 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G4 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q5c r5 t4=t5 at st5 ⊢
  have F5 : ∀q,q∉K.R.T → q∉K.X5 → t5.basis q=t4.basis q := st5.2.2.2
  have G5 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t5.basis q=s.basis q :=
    fun q h hS hT x => (F5 q hT (fun y => x (x5 y))).trans (G4 q h hS hT x)
  have dlo5 : regValue K.R.dlo t5.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo4
  have dhi5 : regValue K.R.dhi t5.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi4
  have S5 : regValue K.R.S t5.basis=a+b := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S4
  -- clean S
  have st6 := K.R.scl1591_correct w hR t5 r6
    (by rw [S5,(outV t5 G5 K.R.lo (fun q h => Or.inl (mt h))).trans ha,(outV t5 G5 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    ((outV t5 G5 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV t5 G5 K.R.carry (by intro q h; simp [h])).trans hc0) ((G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.R.scl1591 r6 t5=t6 at st6 ⊢
  have G6 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t6.basis q=s.basis q :=
    fun q h hS hT x => (st6.2.2 q hS).trans (G5 q h hS hT x)
  have dlo6 : regValue K.R.dlo t6.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo5
  have dhi6 : regValue K.R.dhi t6.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi5
  have T6 : regValue K.R.T t6.basis=0 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st5.2.1
  have X56 : regValue K.X5 t6.basis=0 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st5.2.2.1
  have back6 (q : Wire) (h1 : q∉K.R.S) (h2 : q∉K.R.dst) (h3 : q∉K.R.T) (h4 : q∉K.X5) : t6.basis q=s.basis q :=
    (st6.2.2 q h1).trans ((F5 q h3 h4).trans (back4 q h1 h2 h3))
  -- clear b^2
  have st7 := sp.cl2 t6 r7
    (by rw [dhi6,(outV t6 G6 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    (by rw [(outV t6 G6 K.R.hi (fun q h => Or.inl (md h))).trans hb]
        exact sp.lc2 b s.basis t6.basis (fun q hq => (back6 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) hI2)
    ((outV t6 G6 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t6 G6 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t6 G6 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q2c r7 t6=t7 at st7 ⊢
  have F7 : ∀q,q∉K.R.dhi → q∉K.X2 → t7.basis q=t6.basis q := st7.2.2.2
  have G7 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t7.basis q=s.basis q :=
    fun q h hS hT x => (F7 q (fun y => h (md y)) (fun y => x (x2 y))).trans (G6 q h hS hT x)
  have dlo7 : regValue K.R.dlo t7.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo6
  -- clear a^2
  have st8 := sp.cl1 t7 r8
    (by rw [dlo7,(outV t7 G7 K.R.lo (fun q h => Or.inl (mt h))).trans ha])
    (by rw [(outV t7 G7 K.R.lo (fun q h => Or.inl (mt h))).trans ha]
        exact sp.lc1 a s.basis t7.basis (fun q hq => ((F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).trans (back6 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).symm) hI1)
    ((outV t7 G7 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t7 G7 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t7 G7 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q1c r8 t7=t8 at st8 ⊢
  have F8 : ∀q,q∉K.R.dlo → q∉K.X1 → t8.basis q=t7.basis q := st8.2.2.2
  have k78 (r : List Wire) (h : ∀q∈r,q∉K.R.dlo ∧ q∉K.X1 ∧ q∉K.R.dhi ∧ q∉K.X2) :
      regValue r t8.basis=regValue r t6.basis :=
    regValue_congr _ _ _ (fun q hq => (F8 q (h q hq).1 (h q hq).2.1).trans (F7 q (h q hq).2.2.1 (h q hq).2.2.2))
  refine ⟨st8.1.trans (st7.1.trans (st6.1.trans (st5.1.trans (st4.1.trans (st3.1.trans
    (st2.1.trans st1.1)))))),?_,?_,?_,?_,?_⟩
  · rw [K.R.dst_value w,st8.2.1,(regValue_congr _ _ _ (fun q hq => F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.1]; simp
  · rw [k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩)]; exact st6.2.1
  · rw [k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩)]; exact T6
  · rw [X,regValue_append,regValue_append,st8.2.2.1,
      (regValue_congr _ _ _ (fun q hq => F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.2.1,
      k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩),X56]; simp
  · intro q hd hT hx
    by_cases hS : q∈K.R.S
    · have a1 := (regValue_zero _ _).mp st6.2.1 q hS
      have a2 := (regValue_zero _ _).mp hS0 q hS
      rw [F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS),F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS),a1,a2]
    · exact (F8 q (fun y => hd (mt y)) (fun y => hx (x1 y))).trans (G7 q hd hS hT hx)


theorem make_counts (w : K.R.W) :
    toffoliCount (make K)+3=toffoliCount K.Q1+toffoliCount K.Q2+toffoliCount K.Q5+(kextra K.R.bank.length K.R.h-(K.R.bank.length-K.R.h)) ∧
    measurementCount (make K)=measurementCount K.Q1+measurementCount K.Q2+measurementCount K.Q5+
      kextra K.R.bank.length K.R.h := by
  have p := K.R.piece_counts w
  have z := K.R.scl1591_counts w
  have mz := K.R.m8z_counts w
  have mz7 := K.R.m7y_counts w
  have e : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6++K.R.m7y++K.R.m8z)++K.R.scl1591 := by
    simp only [make,List.append_assoc]
  have q1 := p.2.2.2.2.1
  have q2 := p.2.2.2.2.2.1
  simp only [toffoliCount_append,measurementCount_append] at q1 q2
  rw [e]
  simp only [toffoliCount_append,measurementCount_append,p.1,p.2.1,z.1,z.2,kextra]
  constructor <;> omega

theorem clear_counts (w : K.R.W) :
    toffoliCount (clear K)+3=toffoliCount K.Q1c+toffoliCount K.Q2c+toffoliCount K.Q5c+(kextra K.R.bank.length K.R.h-(K.R.bank.length-K.R.h)) ∧
    measurementCount (clear K)=measurementCount K.Q1c+measurementCount K.Q2c+measurementCount K.Q5c+
      kextra K.R.bank.length K.R.h := by
  have p := K.R.piece_counts w
  have z := K.R.scl1591_counts w
  have mc8 := K.R.c8z_counts w
  have mc7 := K.R.c7y_counts w
  have e : (clear K)=K.R.smk++(K.R.c8z++K.R.c7y++K.R.c6)++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have q1 := p.2.2.2.2.2.2.1
  have q2 := p.2.2.2.2.2.2.2
  simp only [toffoliCount_append,measurementCount_append] at q1 q2
  rw [e]
  simp only [toffoliCount_append,measurementCount_append,p.1,p.2.1,z.1,z.2,kextra]
  constructor <;> omega

theorem r_sub (q : Wire) (h : q∈K.R.all.toFinset) : q∈K.all.toFinset := by
  simp only [List.mem_toFinset,all,List.mem_append] at h ⊢; exact Or.inl h

theorem steps_support (w : K.R.W)
    (s1 : ECDSAAdd.wires K.Q1⊆K.all.toFinset) (s1c : ECDSAAdd.wires K.Q1c⊆K.all.toFinset)
    (s2 : ECDSAAdd.wires K.Q2⊆K.all.toFinset) (s2c : ECDSAAdd.wires K.Q2c⊆K.all.toFinset)
    (s5 : ECDSAAdd.wires K.Q5⊆K.all.toFinset) (s5c : ECDSAAdd.wires K.Q5c⊆K.all.toFinset) :
    ECDSAAdd.wires (make K)⊆K.all.toFinset ∧ ECDSAAdd.wires (clear K)⊆K.all.toFinset := by
  have p := K.R.piece_support w
  have sc := K.R.scl1591_support w
  have e1 : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6++K.R.m7y++K.R.m8z)++K.R.scl1591 := by
    simp only [make,List.append_assoc]
  have e2 : (clear K)=K.R.smk++(K.R.c8z++K.R.c7y++K.R.c6)++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have lift {P : Program} (h : ECDSAAdd.wires P⊆K.R.all.toFinset) : ECDSAAdd.wires P⊆K.all.toFinset :=
    fun q hq => K.r_sub q (h hq)
  have ap {P Q : Program} (h1 : ECDSAAdd.wires P⊆K.all.toFinset) (h2 : ECDSAAdd.wires Q⊆K.all.toFinset) :
      ECDSAAdd.wires (P++Q)⊆K.all.toFinset := by rw [wires_append]; exact Finset.union_subset h1 h2
  have pz : ECDSAAdd.wires (K.R.m6++K.R.m7y++K.R.m8z)⊆K.R.all.toFinset := by
    have h := p.2.2.1
    simp only [wires_append,Finset.union_subset_iff] at h ⊢
    exact ⟨⟨h.1.1,(K.R.m7y_wires).trans h.1.2⟩,(K.R.m8z_wires w).trans h.2⟩
  have cz : ECDSAAdd.wires (K.R.c8z++K.R.c7y++K.R.c6)⊆K.R.all.toFinset := by
    have h := p.2.2.2.1
    simp only [wires_append,Finset.union_subset_iff] at h ⊢
    exact ⟨⟨(K.R.c8z_wires w).trans h.1.1,(K.R.c7y_wires).trans h.1.2⟩,h.2⟩
  rw [e1,e2]
  exact ⟨ap (ap (ap (ap (ap s1 s2) (lift p.1)) s5) (lift pz)) (lift sc),
    ap (ap (ap (ap (ap (lift p.1) (lift cz)) s5c) (lift sc)) s2c) s1c⟩

theorem steps_physical (w : K.R.W) (hn : K.all.Nodup)
    (p1 : GatePhysical K.Q1) (p1c : GatePhysical K.Q1c) (p2 : GatePhysical K.Q2) (p2c : GatePhysical K.Q2c)
    (p5 : GatePhysical K.Q5) (p5c : GatePhysical K.Q5c) :
    GatePhysical (make K) ∧ GatePhysical (clear K) := by
  have p := K.R.piece_physical (K.rnd hn)
  have sc := K.R.scl1591_physical w (K.rnd hn)
  have e1 : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6++K.R.m7y++K.R.m8z)++K.R.scl1591 := by
    simp only [make,List.append_assoc]
  have e2 : (clear K)=K.R.smk++(K.R.c8z++K.R.c7y++K.R.c6)++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have ap {P Q : Program} (h1 : GatePhysical P) (h2 : GatePhysical Q) : GatePhysical (P++Q) :=
    (gatePhysical_append P Q).mpr ⟨h1,h2⟩
  have pz : GatePhysical (K.R.m6++K.R.m7y++K.R.m8z) := by
    have h := p.2.2.1
    simp only [gatePhysical_append] at h ⊢
    exact ⟨⟨h.1.1,K.R.m7y_physical (K.rnd hn)⟩,K.R.m8z_physical (K.rnd hn)⟩
  have cz : GatePhysical (K.R.c8z++K.R.c7y++K.R.c6) := by
    have h := p.2.2.2.1
    simp only [gatePhysical_append] at h ⊢
    exact ⟨⟨K.R.c8z_physical w (K.rnd hn),K.R.c7y_physical (K.rnd hn)⟩,h.2⟩
  rw [e1,e2]
  exact ⟨ap (ap (ap (ap (ap p1 p2) p.1) p5) pz) sc,ap (ap (ap (ap (ap p.1 cz) p5c) sc) p2c) p1c⟩

end ECDSAAdd.Entrant.LowZero18KG

namespace ECDSAAdd.Entrant.LowZero18KG
open Arithmetic KG
variable (K : KG)
theorem steps_slots2 (w : K.R.W) :
    Challenge.gateSlots (make K)+Challenge.gateSlots (clear K) ≤
      Challenge.gateSlots K.Q1+Challenge.gateSlots K.Q1c+Challenge.gateSlots K.Q2+Challenge.gateSlots K.Q2c+
      Challenge.gateSlots K.Q5+Challenge.gateSlots K.Q5c+
      (2*(Challenge.gateSlots K.R.smk+Challenge.gateSlots K.R.scl)+Challenge.gateSlots (K.R.m6++K.R.m7++K.R.m8)+
      Challenge.gateSlots (K.R.c8++K.R.c7++K.R.c6)) := by
  have ms := K.R.m8z_slots w
  have ms7 := K.R.m7y_slots
  have mc8 := K.R.c8z_slots w
  have mc7 := K.R.c7y_slots
  have sc := K.R.scl1591_slots
  simp only [make,clear,Challenge.gateSlots_append] at sc ⊢; omega
end ECDSAAdd.Entrant.LowZero18KG

namespace ECDSAAdd.Entrant.LowZero18KG
open Arithmetic
variable (K : KG)
attribute [local irreducible] toffoliCount measurementCount Challenge.gateSlots wires

theorem make_counts_old (w : K.R.W) :
    toffoliCount (make K)+3=toffoliCount (FrontierSumCleanup1591KG.make K) ∧
    measurementCount (make K)=measurementCount (FrontierSumCleanup1591KG.make K) := by
  have a := make_counts K w
  have b := FrontierSumCleanup1591KG.make_counts K w
  constructor <;> omega

theorem clear_counts_old (w : K.R.W) :
    toffoliCount (clear K)+3=toffoliCount (FrontierSumCleanup1591KG.clear K) ∧
    measurementCount (clear K)=measurementCount (FrontierSumCleanup1591KG.clear K) := by
  have a := clear_counts K w
  have b := FrontierSumCleanup1591KG.clear_counts K w
  constructor <;> omega

theorem make_support_subset (w : K.R.W) :
    wires (make K)⊆wires (FrontierSumCleanup1591KG.make K) := by
  simp only [make,FrontierSumCleanup1591KG.make,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact K.R.m7y_wires | exact K.R.m8z_wires w | exact Finset.Subset.refl _

theorem clear_support_subset (w : K.R.W) :
    wires (clear K)⊆wires (FrontierSumCleanup1591KG.clear K) := by
  simp only [clear,FrontierSumCleanup1591KG.clear,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact K.R.c8z_wires w | exact K.R.c7y_wires | exact Finset.Subset.refl _

theorem make_slots_old (w : K.R.W) :
    Challenge.gateSlots (make K)≤Challenge.gateSlots (FrontierSumCleanup1591KG.make K) := by
  have a := K.R.m7y_slots
  have b := K.R.m8z_slots w
  simp only [make,FrontierSumCleanup1591KG.make,Challenge.gateSlots_append]
  omega

theorem clear_slots_old (w : K.R.W) :
    Challenge.gateSlots (clear K)≤Challenge.gateSlots (FrontierSumCleanup1591KG.clear K) := by
  have a := K.R.c8z_slots w
  have b := K.R.c7y_slots
  simp only [clear,FrontierSumCleanup1591KG.clear,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.LowZero18KG
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18LowK =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18Core
-- consolidated import: import ECDSAAdd.Submission.Entrant.SquareCarryLoan719BFProof

-- DIAGONAL COMPONENT LowK.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
section
namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

/-- Fold-pad tail: untouched by the leaf producer and cleanup, used only for clean-at-rest scratch. -/
def ktmp (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldPad.drop 131

def oregs (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=64,bank:=L.inputBank.take src.length,dst:=dst,
   S:=((ktmp L).take 66).take (src.length-63),
   T:=(ext.take 132).take (2*(src.length-63)),
   z:=(L.leafCarry.drop 193).take 62,
   pad:=L.leafPad,carry:=L.leafCarry.take 193,cin:=L.core.cin}

def iregs (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=32,bank:=(oregs L ext src dst).lo,dst:=(oregs L ext src dst).dlo,
   S:=((ktmp L).drop 66).take 33,T:=(ext.drop 132).take 66,
   z:=(oregs L ext src dst).z.take 30,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

def jregsH (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=32,bank:=(oregs L ext src dst).hi,dst:=(oregs L ext src dst).dhi,
   S:=((ext.drop 198).take 34).take 33,T:=(ext.drop 232).take 66,
   z:=(oregs L ext src dst).z.take 30,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

def jregsS (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=33,bank:=(oregs L ext src dst).S,dst:=(oregs L ext src dst).T,
   S:=(ext.drop 198).take 34,T:=(ext.drop 232).take 68,
   z:=(oregs L ext src dst).z.take 31,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

/-- 128-bit leaves: nested split of the low and high halves, cleaned low inner sum. -/
def kgH (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  {R:=oregs L ext src dst,X1:=(iregs L ext src dst).S++(iregs L ext src dst).T,
   X2:=(jregsH L ext src dst).S++(jregsH L ext src dst).T,X5:=[],
   Q1:=LowZero18Diagonal.makeC (iregs L ext src dst),Q1c:=LowZero18Diagonal.clearC (iregs L ext src dst),
   Q2:=LowZero18Diagonal.make (jregsH L ext src dst),Q2c:=LowZero18Diagonal.clear (jregsH L ext src dst),
   Q5:=TrimSquare3.tsq3 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,Q5c:=TrimSquare3.tsqc3 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,
   I1:=(iregs L ext src dst).invC,I2:=(jregsH L ext src dst).invF,I5:=fun _ _ => True}

/-- 129-bit leaf: nested split of the low half and of the sum square, cleaned low inner sum. -/
def kgS (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  {R:=oregs L ext src dst,X1:=(iregs L ext src dst).S++(iregs L ext src dst).T,
   X2:=[],X5:=(jregsS L ext src dst).S++(jregsS L ext src dst).T,
   Q1:=LowZero18Diagonal.makeC (iregs L ext src dst),Q1c:=LowZero18Diagonal.clearC (iregs L ext src dst),
   Q2:=TrimSquare3.tsq3 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,Q2c:=TrimSquare3.tsqc3 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,
   Q5:=LowZero18Diagonal.make (jregsS L ext src dst),Q5c:=LowZero18Diagonal.clear (jregsS L ext src dst),
   I1:=(iregs L ext src dst).invC,I2:=fun _ _ => True,I5:=(jregsS L ext src dst).invF}

def kg (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  if src.length=128 then kgH L ext src dst else kgS L ext src dst

theorem ktmp_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (ktmp L).length=123 := by
  simp [ktmp,L.foldPad_length hw]

theorem oregs_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (oregs L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [oregs,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl] <;> omega

theorem iregs_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (iregs L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [iregs,oregs,KRegs.lo,KRegs.dlo,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl] <;> omega

theorem jregsH_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : src.length=128) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (jregsH L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [jregsH,oregs,KRegs.hi,KRegs.dhi,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl,h128] <;> omega

theorem jregsS_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h129 : src.length=129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (jregsS L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [jregsS,oregs,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl,h129] <;> omega

theorem tmp_count (L : CuccaroStreamedSquareWideLayout) (n : Nat) (q : Wire) :
    (L.inputBank.take n++L.leafPad++L.leafCarry++ktmp L).count q≤
      L.core.work.count q+L.foldPad.count q := by
  have inputBound := (List.take_sublist n L.inputBank).count_le q
  have workSplit := congrArg (List.count q) (List.take_append_drop 129 L.core.work)
  have padSplit := congrArg (List.count q) (List.take_append_drop 1 L.foldPad)
  have tailSplit := congrArg (List.count q) (List.take_append_drop 130 (L.foldPad.drop 1))
  have hdd : (L.foldPad.drop 1).drop 130=L.foldPad.drop 131 := by simp [List.drop_drop]
  rw [hdd] at tailSplit
  simp only [inputBank,leafPad,leafCarry,ktmp,List.count_append] at inputBound workSplit padSplit tailSplit ⊢
  omega

def kbig2 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) : List Wire :=
  (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++ktmp L)++ext

theorem lst_le2 (L : CuccaroStreamedSquareWideLayout) (control : Wire) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) (q : Wire) :
    (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++ktmp L).count q ≤
      (control::L.wires).count q := by
  have a := hs q
  have b := hd q
  have banks := tmp_count L src.length q
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,List.count_cons,
    List.count_append,List.count_nil] at a banks ⊢
  omega

theorem kbig2_nodup (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) (ext : List Wire) (hx : ext.Nodup)
    (hdx : ∀q∈ext,q∉control::L.wires) : (kbig2 L ext control src dst).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have b := List.nodup_iff_count_le_one.mp hx q
  have c := lst_le2 L control src dst hs hd q
  have d := List.nodup_iff_count_le_one.mp hn q
  simp only [kbig2,List.count_append] at c ⊢
  by_cases hq : q∈ext
  · have z : (control::L.wires).count q=0 := List.count_eq_zero.mpr (hdx q hq)
    omega
  · have z : ext.count q=0 := List.count_eq_zero.mpr hq
    omega

theorem ktmp_wires (L : CuccaroStreamedSquareWideLayout) (q : Wire) (h : q∈ktmp L) : q∈L.wires := by
  have h' : q∈L.foldPad := List.mem_of_mem_drop h
  simp only [foldPad,List.mem_append] at h'
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_append,List.mem_cons]
  tauto

theorem ext_split4 (ext : List Wire) (a b c : Nat) (q : Wire) :
    ((ext.take 132).take a).count q+((ext.drop 132).take 66).count q+
      (((ext.drop 198).take 34).take b).count q+((ext.drop 232).take c).count q≤ext.count q := by
  have x1 := kcnt_take (ext.take 132) a q
  have x2 := kcnt_take ((ext.drop 198).take 34) b q
  have x3 := kcnt_take (ext.drop 232) c q
  have e1 := kcnt_split ext 132 q
  have e2 := kcnt_split (ext.drop 132) 66 q
  have e3 := kcnt_split (ext.drop 198) 34 q
  have e4 := kcnt_take (ext.drop 132) 66 q
  simp only [List.drop_drop] at e2 e3
  norm_num at e2 e3
  omega

theorem tmp_split2 (L : CuccaroStreamedSquareWideLayout) (a : Nat) (q : Wire) :
    (((ktmp L).take 66).take a).count q+(((ktmp L).drop 66).take 33).count q≤(ktmp L).count q := by
  have x1 := kcnt_take ((ktmp L).take 66) a q
  have x2 := kcnt_take ((ktmp L).drop 66) 33 q
  have e := kcnt_split (ktmp L) 66 q
  omega

theorem carry_split (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (L.leafCarry.take 193).count q+((L.leafCarry.drop 193).take 62).count q≤L.leafCarry.count q := by
  have x := kcnt_take (L.leafCarry.drop 193) 62 q
  have e := kcnt_split L.leafCarry 193 q
  omega

end ECDSAAdd.Entrant.LowZero18LowK

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs




theorem sub_of_count {l l' : List Wire} (h : ∀q,l.count q≤l'.count q) : l.toFinset⊆l'.toFinset := by
  intro q hq
  have a := List.count_pos_iff.mpr (List.mem_toFinset.mp hq)
  exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by have := h q; omega))

section Inst
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

include hn hs hd hx hdx in
theorem kgH_nodup : (kgH L ext src dst).all.Nodup :=
  knd (kbig2_nodup L control hn src dst hs hd ext hx hdx) (fun q => by
    have a := ext_split4 ext (2*(src.length-63)) 33 66 q
    have b := tmp_split2 L (src.length-63) q
    have c := carry_split L q
    simp only [KG.all,KG.X,kgH,KRegs.all,oregs,iregs,jregsH,kbig2,List.count_cons,List.count_append,List.count_nil] at a b c ⊢
    omega)

include hn hs hd hx hdx in
theorem kgS_nodup : (kgS L ext src dst).all.Nodup :=
  knd (kbig2_nodup L control hn src dst hs hd ext hx hdx) (fun q => by
    have a := ext_split4 ext (2*(src.length-63)) 34 68 q
    have b := tmp_split2 L (src.length-63) q
    have c := carry_split L q
    have e : List.count q (((ext.drop 198).take 34).take 34)=List.count q ((ext.drop 198).take 34) := by
      rw [List.take_take,Nat.min_self]
    simp only [KG.all,KG.X,kgS,KRegs.all,oregs,iregs,jregsS,kbig2,List.count_cons,List.count_append,List.count_nil] at a b c e ⊢
    omega)

theorem kgH_iall (q : Wire) :
    (iregs L ext src dst).all.count q≤(kgH L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgH,KRegs.all,iregs,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgH_jall (q : Wire) :
    (jregsH L ext src dst).all.count q≤(kgH L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgH,KRegs.all,jregsH,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgS_iall (q : Wire) :
    (iregs L ext src dst).all.count q≤(kgS L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgS,KRegs.all,iregs,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgS_jall (q : Wire) :
    (jregsS L ext src dst).all.count q≤(kgS L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 31 q
  simp only [KG.all,KG.X,kgS,KRegs.all,jregsS,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega

include hw h128 hsmax hlen he in
theorem kgH_spec (h : src.length=128) (hall : (kgH L ext src dst).all.Nodup) : (kgH L ext src dst).Spec := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsH_W L hw ext src dst h hlen he
  have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
  have ni : (iregs L ext src dst).all.Nodup := knd hall (kgH_iall L ext src dst)
  have nj : (jregsH L ext src dst).all.Nodup := knd hall (kgH_jall L ext src dst)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hh := w.hh; have h4 := w.h4
  have n5 : ((oregs L ext src dst).cin::(oregs L ext src dst).S++(oregs L ext src dst).T++
      (oregs L ext src dst).pad++(oregs L ext src dst).carry).Nodup :=
    knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  exact ⟨w,LowZero18Diagonal.diag_sq_cl_make (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    LowZero18Diagonal.diag_sq_cl_clear (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).invC_local,
    LowZero18Diagonal.diag_sq_full_make (jregsH L ext src dst) wj (by have sz := L.measured_bank_widths hw; simp only [jregsH,oregs,KRegs.hi,List.length_take,List.length_drop,sz.1,h]; omega) (Or.inl rfl) nj _ (fun q h => List.mem_of_mem_take h),
    LowZero18Diagonal.diag_sq_full_clear (jregsH L ext src dst) wj (by have sz := L.measured_bank_widths hw; simp only [jregsH,oregs,KRegs.hi,List.length_take,List.length_drop,sz.1,h]; omega) (Or.inl rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsH L ext src dst).invF_local,
    sq_plain3_make (oregs L ext src dst).cin (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n5 (by omega) (by omega) hpl (by omega),
    sq_plain3_clear (oregs L ext src dst).cin (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n5 (by omega) (by omega) hpl (by omega),
    sq_plain_local⟩

include hw h128 hsmax hlen he in
theorem kgS_spec (h : src.length=129) (hall : (kgS L ext src dst).all.Nodup) : (kgS L ext src dst).Spec := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsS_W L hw ext src dst h hlen he
  have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
  have ni : (iregs L ext src dst).all.Nodup := knd hall (kgS_iall L ext src dst)
  have nj : (jregsS L ext src dst).all.Nodup := knd hall (kgS_jall L ext src dst)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hh := w.hh; have h4 := w.h4
  have hdl := w.dst
  have n2 : ((oregs L ext src dst).cin::(oregs L ext src dst).hi++(oregs L ext src dst).dhi++
      (oregs L ext src dst).pad++(oregs L ext src dst).carry).Nodup :=
    knd hR (fun q => by have c := (oregs L ext src dst).counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  exact ⟨w,LowZero18Diagonal.diag_sq_cl_make (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    LowZero18Diagonal.diag_sq_cl_clear (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).invC_local,
    sq_plain3_make (oregs L ext src dst).cin (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n2 (by omega) (by omega) hpl (by omega),
    sq_plain3_clear (oregs L ext src dst).cin (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n2 (by omega) (by omega) hpl (by omega),
    sq_plain_local,
    LowZero18Diagonal.diag_sq_full_make (jregsS L ext src dst) wj (by simp only [jregsS,oregs,List.length_take,ktmp_length L hw,h]; norm_num) (Or.inr rfl) nj _ (fun q h => List.mem_of_mem_take h),
    LowZero18Diagonal.diag_sq_full_clear (jregsS L ext src dst) wj (by simp only [jregsS,oregs,List.length_take,ktmp_length L hw,h]; norm_num) (Or.inr rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsS L ext src dst).invF_local⟩

end Inst
end ECDSAAdd.Entrant.LowZero18LowK

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

section Inst3
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (he : 300≤ext.length)

attribute [local irreducible] toffoliCount measurementCount

include hw in
theorem oregs_lens (h : 128≤src.length) (h2 : src.length≤129) :
    (oregs L ext src dst).h=64 ∧ (oregs L ext src dst).bank.length=src.length := by
  have sz := L.measured_bank_widths hw
  refine ⟨rfl,?_⟩
  simp only [oregs,List.length_take,sz.1]; omega

include hw h128 hsmax hlen he in
theorem kgH_counts (h : src.length=128) :
    toffoliCount (LowZero18KG.make (kgH L ext src dst))=6573 ∧ measurementCount (LowZero18KG.make (kgH L ext src dst))=6684 ∧
    toffoliCount (LowZero18KG.clear (kgH L ext src dst))=6541 ∧ measurementCount (LowZero18KG.clear (kgH L ext src dst))=6684 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsH_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have mk := LowZero18KG.make_counts (kgH L ext src dst) w
  have cl := LowZero18KG.clear_counts (kgH L ext src dst) w
  have i1 := LowZero18Diagonal.make_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := LowZero18Diagonal.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have ip0 := (iregs L ext src dst).scl1591_counts wi
  have j1 := LowZero18Diagonal.make_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have j2 := LowZero18Diagonal.clear_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have q := TrimSquare3.tsq3_counts (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsH L ext src dst).h=32 := rfl
  simp only [DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip ip0
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30)-10 ∧ measurementCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30)-4+32 ∧
      toffoliCount (kgH L ext src dst).Q1c=(raw_kcost 64 32-30)-10 ∧ measurementCount (kgH L ext src dst).Q1c=32+((raw_kcost 64 32-30)-4) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [toffoliCount_append,ip0.1]; have := i1.1; omega
    · show measurementCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [measurementCount_append,ip0.2]; have := i1.2; omega
    · show toffoliCount ((iregs L ext src dst).smk++(LowZero18Diagonal.clear (iregs L ext src dst)))=_; rw [toffoliCount_append,i2.1,ip.1]; norm_num [raw_kcost,raw_ksq,signedSquareRowsCount]
    · show measurementCount ((iregs L ext src dst).smk++(Z5Diagonal.clear (iregs L ext src dst)))=_; rw [measurementCount_append,ip.2.1]; have := i2.2; omega
  have t2 : toffoliCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30)-10 ∧ measurementCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30)-4 ∧
      toffoliCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30)-32-10 ∧ measurementCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30)-4 :=
    ⟨j1.1,j1.2,j2.1,Nat.eq_sub_of_add_eq j2.2⟩
  have t5 : toffoliCount (kgH L ext src dst).Q5=ksq 65-1 ∧ measurementCount (kgH L ext src dst).Q5=ksq 65-1 ∧
      toffoliCount (kgH L ext src dst).Q5c=ksq 65-1 ∧ measurementCount (kgH L ext src dst).Q5c=ksq 65-1 := by
    have e : (oregs L ext src dst).S.length=65 := by omega
    have f : (oregs L ext src dst).T.length=130 := by omega
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (TrimSquare3.tsq3 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.1.1,e,f]; rfl
    · show measurementCount (TrimSquare3.tsq3 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.1.2,e,f]; rfl
    · show toffoliCount (TrimSquare3.tsqc3 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.2.1,e,f]; rfl
    · show measurementCount (TrimSquare3.tsqc3 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.2.2,e,f]; rfl
  have rb : (kgH L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgH L ext src dst).R.h=64 := rfl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  refine ⟨?_,?_,?_,?_⟩ <;> omega

include hw h128 hsmax hlen he in
theorem kgS_counts (h : src.length=129) :
    toffoliCount (LowZero18KG.make (kgS L ext src dst))=6690 ∧ measurementCount (LowZero18KG.make (kgS L ext src dst))=6802 ∧
    toffoliCount (LowZero18KG.clear (kgS L ext src dst))=6657 ∧ measurementCount (LowZero18KG.clear (kgS L ext src dst))=6802 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsS_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have mk := LowZero18KG.make_counts (kgS L ext src dst) w
  have cl := LowZero18KG.clear_counts (kgS L ext src dst) w
  have i1 := LowZero18Diagonal.make_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := LowZero18Diagonal.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have ip0 := (iregs L ext src dst).scl1591_counts wi
  have j1 := LowZero18Diagonal.make_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have j2 := LowZero18Diagonal.clear_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have q := TrimSquare3.tsq3_counts (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsS L ext src dst).h=33 := rfl
  simp only [DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip ip0
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30)-10 ∧ measurementCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30)-4+32 ∧
      toffoliCount (kgS L ext src dst).Q1c=(raw_kcost 64 32-30)-10 ∧ measurementCount (kgS L ext src dst).Q1c=32+((raw_kcost 64 32-30)-4) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [toffoliCount_append,ip0.1]; have := i1.1; omega
    · show measurementCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [measurementCount_append,ip0.2]; have := i1.2; omega
    · show toffoliCount ((iregs L ext src dst).smk++(LowZero18Diagonal.clear (iregs L ext src dst)))=_; rw [toffoliCount_append,i2.1,ip.1]; norm_num [raw_kcost,raw_ksq,signedSquareRowsCount]
    · show measurementCount ((iregs L ext src dst).smk++(Z5Diagonal.clear (iregs L ext src dst)))=_; rw [measurementCount_append,ip.2.1]; have := i2.2; omega
  have t2 : toffoliCount (kgS L ext src dst).Q2=ksq 65-1 ∧ measurementCount (kgS L ext src dst).Q2=ksq 65-1 ∧
      toffoliCount (kgS L ext src dst).Q2c=ksq 65-1 ∧ measurementCount (kgS L ext src dst).Q2c=ksq 65-1 := by
    have e : (oregs L ext src dst).hi.length=65 := by omega
    have f : (oregs L ext src dst).dhi.length=130 := by omega
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (TrimSquare3.tsq3 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.1.1,e,f]; rfl
    · show measurementCount (TrimSquare3.tsq3 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.1.2,e,f]; rfl
    · show toffoliCount (TrimSquare3.tsqc3 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.2.1,e,f]; rfl
    · show measurementCount (TrimSquare3.tsqc3 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; rw [q.2.2,e,f]; rfl
  have t5 : toffoliCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31)-10 ∧ measurementCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31)-4 ∧
      toffoliCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31)-33-10 ∧ measurementCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31)-4 :=
    ⟨j1.1,j1.2,j2.1,Nat.eq_sub_of_add_eq j2.2⟩
  have rb : (kgS L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgS L ext src dst).R.h=64 := rfl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  refine ⟨?_,?_,?_,?_⟩ <;> omega

end Inst3
end ECDSAAdd.Entrant.LowZero18LowK

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

section Inst4
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

theorem kg_R : (kg L ext src dst).R=oregs L ext src dst := by
  unfold kg; split <;> rfl

theorem kg_I1 : (kg L ext src dst).I1=(iregs L ext src dst).invC := by
  unfold kg; split <;> rfl

theorem kg_X (q : Wire) (h : q∈(kg L ext src dst).X) : q∈ext ∨ q∈((ktmp L).drop 66).take 33 := by
  by_cases c : src.length=128
  · rw [kg,if_pos c] at h
    simp only [KG.X] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact Or.inr h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 132).take 66)))
      · rcases List.mem_append.mp h with h|h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take (h : q∈((ext.drop 198).take 34).take 33))))
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 232).take 66)))
    · exact absurd h (List.not_mem_nil)
  · rw [kg,if_neg c] at h
    simp only [KG.X] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact Or.inr h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 132).take 66)))
      · exact absurd h (List.not_mem_nil)
    · rcases List.mem_append.mp h with h|h
      · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 198).take 34)))
      · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 232).take 68)))

include hn hs hd hx hdx in
theorem kg_nodup : (kg L ext src dst).all.Nodup := by
  by_cases c : src.length=128
  · rw [kg,if_pos c]; exact kgH_nodup L control hn ext src dst hs hd hx hdx
  · rw [kg,if_neg c]; exact kgS_nodup L control hn ext src dst hs hd hx hdx

include hw h128 hsmax hlen he in
theorem kg_spec (hall : (kg L ext src dst).all.Nodup) : (kg L ext src dst).Spec := by
  by_cases c : src.length=128
  · rw [kg,if_pos c] at hall ⊢; exact kgH_spec L hw ext src dst h128 hsmax hlen he c hall
  · rw [kg,if_neg c] at hall ⊢; exact kgS_spec L hw ext src dst h128 hsmax hlen he (by omega) hall

def lowkcost2 (n : Nat) : Nat := if n=128 then 6684 else 6802
def lowkcostTMake (n : Nat) : Nat := if n=128 then 6573 else 6690
def lowkcostTClear (n : Nat) : Nat := if n=128 then 6541 else 6657
def lowkcostTPair (n : Nat) : Nat := lowkcostTMake n+lowkcostTClear n

include hw h128 hsmax hlen he in
theorem kg_counts :
    toffoliCount (LowZero18KG.make (kg L ext src dst))=lowkcostTMake src.length ∧
    measurementCount (LowZero18KG.make (kg L ext src dst))=lowkcost2 src.length ∧
    toffoliCount (LowZero18KG.clear (kg L ext src dst))=lowkcostTClear src.length ∧
    measurementCount (LowZero18KG.clear (kg L ext src dst))=lowkcost2 src.length := by
  by_cases c : src.length=128
  · simp only [kg,lowkcost2,lowkcostTMake,lowkcostTClear,if_pos c]; exact kgH_counts L hw ext src dst h128 hsmax hlen he c
  · simp only [kg,lowkcost2,lowkcostTMake,lowkcostTClear,if_neg c]; exact kgS_counts L hw ext src dst h128 hsmax hlen he (by omega)

include hw h128 hsmax hlen he in
theorem kg_support :
    ECDSAAdd.wires (LowZero18KG.make (kg L ext src dst))⊆(kg L ext src dst).all.toFinset ∧
    ECDSAAdd.wires (LowZero18KG.clear (kg L ext src dst))⊆(kg L ext src dst).all.toFinset := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have rp := (oregs L ext src dst).piece_support w
  have ip := (iregs L ext src dst).piece_support wi
  have is := LowZero18Diagonal.steps_support (iregs L ext src dst) wi
  have isc := (iregs L ext src dst).scl1591_support wi
  have tr {P : Program} {A B : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : A⊆B) : ECDSAAdd.wires P⊆B := h1.trans h2
  have ap {P Q : Program} {A : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : ECDSAAdd.wires Q⊆A) :
      ECDSAAdd.wires (P++Q)⊆A := by rw [wires_append]; exact Finset.union_subset h1 h2
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have js := LowZero18Diagonal.steps_support (jregsH L ext src dst) wj
    have iK := sub_of_count (kgH_iall L ext src dst)
    have jK := sub_of_count (kgH_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgH L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact LowZero18KG.steps_support _ w (ap (tr is.1 iK) (tr isc iK)) (ap (tr ip.1 iK) (tr is.2 iK))
      (tr js.1 jK) (tr js.2 jK) (tr ((TrimSquare3.tsq3_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1.trans rp.2.2.2.2.2.2.1) rK) (tr ((TrimSquare3.tsq3_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).2.trans rp.2.2.2.2.2.2.2) rK)
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have js := LowZero18Diagonal.steps_support (jregsS L ext src dst) wj
    have iK := sub_of_count (kgS_iall L ext src dst)
    have jK := sub_of_count (kgS_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgS L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact LowZero18KG.steps_support _ w (ap (tr is.1 iK) (tr isc iK)) (ap (tr ip.1 iK) (tr is.2 iK))
      (tr ((TrimSquare3.tsq3_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1.trans rp.2.2.2.2.1) rK) (tr ((TrimSquare3.tsq3_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).2.trans rp.2.2.2.2.2.1) rK) (tr js.1 jK) (tr js.2 jK)

include hw h128 hsmax hlen he in
theorem kg_physical (hall : (kg L ext src dst).all.Nodup) :
    GatePhysical (LowZero18KG.make (kg L ext src dst)) ∧ GatePhysical (LowZero18KG.clear (kg L ext src dst)) := by
  have ap {P Q : Program} (h1 : GatePhysical P) (h2 : GatePhysical Q) : GatePhysical (P++Q) :=
    (gatePhysical_append P Q).mpr ⟨h1,h2⟩
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  by_cases h : src.length=128
  · rw [kg,if_pos h] at hall ⊢
    have wj := jregsH_W L hw ext src dst h hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgH_iall L ext src dst)
    have nj := knd hall (kgH_jall L ext src dst)
    have rp := (oregs L ext src dst).piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := LowZero18Diagonal.steps_physical (iregs L ext src dst) wi ni
    have isc := (iregs L ext src dst).scl1591_physical wi ni
    have js := LowZero18Diagonal.steps_physical (jregsH L ext src dst) wj nj
    exact LowZero18KG.steps_physical _ (oregs_W L hw ext src dst h128 hsmax hlen he) hall (ap is.1 isc) (ap ip.1 is.2) js.1 js.2 (TrimSquare3.tsq3_physical_of (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.2.2.1 rp.2.2.2.2.2.2.2).1 (TrimSquare3.tsq3_physical_of (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.2.2.1 rp.2.2.2.2.2.2.2).2
  · rw [kg,if_neg h] at hall ⊢
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgS_iall L ext src dst)
    have nj := knd hall (kgS_jall L ext src dst)
    have rp := (oregs L ext src dst).piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := LowZero18Diagonal.steps_physical (iregs L ext src dst) wi ni
    have isc := (iregs L ext src dst).scl1591_physical wi ni
    have js := LowZero18Diagonal.steps_physical (jregsS L ext src dst) wj nj
    exact LowZero18KG.steps_physical _ (oregs_W L hw ext src dst h128 hsmax hlen he) hall (ap is.1 isc) (ap ip.1 is.2) (TrimSquare3.tsq3_physical_of (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.1 rp.2.2.2.2.2.1).1 (TrimSquare3.tsq3_physical_of (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.1 rp.2.2.2.2.2.1).2 js.1 js.2

include hw h128 hsmax hlen he in
theorem kg_slots :
    Challenge.gateSlots (LowZero18KG.make (kg L ext src dst))+Challenge.gateSlots (LowZero18KG.clear (kg L ext src dst))≤1200000 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have ol := oregs_lens L hw ext src dst h128 hsmax
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T
  have ad := (oregs L ext src dst).adder_slots w rfl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have it := LowZero18Diagonal.tiny_slots (iregs L ext src dst) wi (by rw [il,ih]) (by rw [ih]; omega)
  simp only [LowZero18Diagonal.clear] at it
  have oldit := (iregs L ext src dst).tiny_slots wi (by rw [ih]; omega) (by rw [il,ih]; omega) (by omega)
  have isb := (iregs L ext src dst).make_sub_slots wi
  have isc := (iregs L ext src dst).scl1591_slots
  have g2 := TrimSquare3.tsq3_gateSlots_le (oregs L ext src dst).hi (oregs L ext src dst).dhi
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g5 := TrimSquare3.tsq3_gateSlots_le (oregs L ext src dst).S (oregs L ext src dst).T
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have x2 : (oregs L ext src dst).hi.length*(12*((oregs L ext src dst).hi.length+1)+6*(oregs L ext src dst).dhi.length) ≤ 65*(12*66+6*130) :=
    Nat.mul_le_mul (by omega) (by omega)
  have x5 : (oregs L ext src dst).S.length*(12*((oregs L ext src dst).S.length+1)+6*(oregs L ext src dst).T.length) ≤ 66*(12*67+6*132) :=
    Nat.mul_le_mul (by omega) (by omega)
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
    have jh : (jregsH L ext src dst).h=32 := rfl
    have jt := LowZero18Diagonal.tiny_slots (jregsH L ext src dst) wj (by rw [jl,jh]) (by omega)
    simp only [LowZero18Diagonal.clear] at jt
    have st := LowZero18KG.steps_slots2 (kgH L ext src dst) w
    simp only [kgH,LowZero18Diagonal.makeC,LowZero18Diagonal.clearC,LowZero18Diagonal.clear,Z5Diagonal.clearC,KRegs.m5,KRegs.c5,Challenge.gateSlots_append] at st ad ⊢
    omega
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
    have jh : (jregsS L ext src dst).h=33 := rfl
    have jt := LowZero18Diagonal.tiny_slots (jregsS L ext src dst) wj (by rw [jl,jh]) (by omega)
    simp only [LowZero18Diagonal.clear] at jt
    have st := LowZero18KG.steps_slots2 (kgS L ext src dst) w
    simp only [kgS,LowZero18Diagonal.makeC,LowZero18Diagonal.clearC,LowZero18Diagonal.clear,Z5Diagonal.clearC,KRegs.m2,KRegs.c2,Challenge.gateSlots_append] at st ad ⊢
    omega

end Inst4
end ECDSAAdd.Entrant.LowZero18LowK


namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem kg_metadata (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    (kg L ext src dst).R=(FrontierSumCleanup1591LowK.kg L ext src dst).R ∧
    (kg L ext src dst).X1=(FrontierSumCleanup1591LowK.kg L ext src dst).X1 ∧
    (kg L ext src dst).X=(FrontierSumCleanup1591LowK.kg L ext src dst).X ∧
    (kg L ext src dst).all=(FrontierSumCleanup1591LowK.kg L ext src dst).all := by
  by_cases h : src.length=128
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true];exact ⟨rfl,rfl,rfl,rfl⟩
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false];exact ⟨rfl,rfl,rfl,rfl⟩

theorem kg_Q1c_subset (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    wires (kg L ext src dst).Q1c⊆wires (FrontierSumCleanup1591LowK.kg L ext src dst).Q1c := by
  have a := LowZero18Diagonal.clearC_support_subset (iregs L ext src dst)
  by_cases h : src.length=128
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,kgH,FrontierSumCleanup1591LowK.kgH] using a
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,kgS,FrontierSumCleanup1591LowK.kgS] using a

theorem kg_Q1_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (kg L ext src dst).Q1⊆wires (FrontierSumCleanup1591LowK.kg L ext src dst).Q1 := by
  have wi := iregs_W L hw ext src dst h128 h129 hd he
  have a := LowZero18Diagonal.makeC_support_subset (iregs L ext src dst) wi
  by_cases h : src.length=128
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,kgH,FrontierSumCleanup1591LowK.kgH] using a
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,kgS,FrontierSumCleanup1591LowK.kgS] using a

theorem kg_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (LowZero18KG.make (kg L ext src dst))+24=
      toffoliCount (FrontierSumCleanup1591KG.make (FrontierSumCleanup1591LowK.kg L ext src dst)) ∧
    measurementCount (LowZero18KG.make (kg L ext src dst))+9=
      measurementCount (FrontierSumCleanup1591KG.make (FrontierSumCleanup1591LowK.kg L ext src dst)) ∧
    toffoliCount (LowZero18KG.clear (kg L ext src dst))+24=
      toffoliCount (FrontierSumCleanup1591KG.clear (FrontierSumCleanup1591LowK.kg L ext src dst)) ∧
    measurementCount (LowZero18KG.clear (kg L ext src dst))+9=
      measurementCount (FrontierSumCleanup1591KG.clear (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have a := kg_counts L hw ext src dst h128 h129 hd he
  have b := FrontierSumCleanup1591LowK.kg_counts L hw ext src dst h128 h129 hd he
  by_cases h : src.length=128
  all_goals simp only [lowkcostTMake,lowkcostTClear,lowkcost2,FrontierSumCleanup1591LowK.lowkcostTMake,
    FrontierSumCleanup1591LowK.lowkcostTClear,FrontierSumCleanup1591LowK.lowkcost2,h,ite_true,ite_false] at a b
  all_goals exact ⟨by omega,by omega,by omega,by omega⟩

end ECDSAAdd.Entrant.LowZero18LowK

end


namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] wires toffoliCount measurementCount Challenge.gateSlots

theorem loan_make_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    wires (LowZero18KG.make (SquareCarryLoan719.patchKG L (kg L ext src dst)))⊆
      wires (SquareCarryLoan719BF.make L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have wi := iregs_W L hw ext src dst h128 h129 hd he
  have ip := OneFlagReplay.rename_subset (SquareCarryLoan719.earlyPerm L) _ _
    (LowZero18Diagonal.makeC_support_subset (iregs L ext src dst) wi)
  by_cases h : src.length=128
  · have jp := LowZero18Diagonal.make_support_subset (jregsH L ext src dst)
      (jregsH_W L hw ext src dst h hd he)
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgH,FrontierSumCleanup1591LowK.kgH,KRegs.m5,wires_append]
    repeat' apply Finset.union_subset_union
    all_goals first | exact ip | exact jp | exact (TrimSquare3.tsq3_wires_le _ _ _ _ _).1 | exact (oregs L ext src dst).m7y_wires |
      exact (oregs L ext src dst).m8z_wires w | exact Finset.Subset.refl _
  · have jp := LowZero18Diagonal.make_support_subset (jregsS L ext src dst)
      (jregsS_W L hw ext src dst (by omega) hd he)
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgS,FrontierSumCleanup1591LowK.kgS,KRegs.m2,wires_append]
    repeat' apply Finset.union_subset_union
    all_goals first | exact ip | exact jp | exact (TrimSquare3.tsq3_wires_le _ _ _ _ _).1 | exact (oregs L ext src dst).m7y_wires |
      exact (oregs L ext src dst).m8z_wires w | exact Finset.Subset.refl _

theorem loan_clear_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    wires (LowZero18KG.clear (SquareCarryLoan719.patchKG L (kg L ext src dst)))⊆
      wires (SquareCarryLoan719BF.clear L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have ipc := OneFlagReplay.rename_subset (SquareCarryLoan719.earlyPerm L) _ _
    (LowZero18Diagonal.clearC_support_subset (iregs L ext src dst))
  have jhc := LowZero18Diagonal.clear_support_subset (jregsH L ext src dst)
  have jsc := LowZero18Diagonal.clear_support_subset (jregsS L ext src dst)
  by_cases h : src.length=128
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,LowZero18KG.clear,
      SquareCarryLoan719BF.clear,FrontierSumCleanup1591KG.clear,SquareCarryLoan719.patchKG,
      kgH,FrontierSumCleanup1591LowK.kgH,KRegs.c5,wires_append]
    repeat' apply Finset.union_subset_union
    all_goals first | exact ipc | exact jhc | exact (TrimSquare3.tsq3_wires_le _ _ _ _ _).2 | exact (oregs L ext src dst).c8z_wires w |
      exact (oregs L ext src dst).c7y_wires | exact Finset.Subset.refl _
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,LowZero18KG.clear,
      SquareCarryLoan719BF.clear,FrontierSumCleanup1591KG.clear,SquareCarryLoan719.patchKG,
      kgS,FrontierSumCleanup1591LowK.kgS,KRegs.c2,wires_append]
    repeat' apply Finset.union_subset_union
    all_goals first | exact ipc | exact jsc | exact (TrimSquare3.tsq3_wires_le _ _ _ _ _).2 | exact (oregs L ext src dst).c8z_wires w |
      exact (oregs L ext src dst).c7y_wires | exact Finset.Subset.refl _

theorem loan_make_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18KG.make (SquareCarryLoan719.patchKG L (kg L ext src dst)))≤
      Challenge.gateSlots (SquareCarryLoan719BF.make L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have wi := iregs_W L hw ext src dst h128 h129 hd he
  have ip := LowZero18Diagonal.makeC_slots_old (iregs L ext src dst) wi
  have a := (oregs L ext src dst).m7y_slots
  have b := (oregs L ext src dst).m8z_slots w
  have q5 := TrimSquare3.tsq3_slots_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q2 := TrimSquare3.tsq3_slots_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have ro : oregs L ext src dst=FrontierSumCleanup1591LowK.oregs L ext src dst := rfl
  have ri : iregs L ext src dst=FrontierSumCleanup1591LowK.iregs L ext src dst := rfl
  by_cases h : src.length=128
  · have jp := LowZero18Diagonal.make_slots_le (jregsH L ext src dst)
      (jregsH_W L hw ext src dst h hd he)
    have rj : jregsH L ext src dst=FrontierSumCleanup1591LowK.jregsH L ext src dst := rfl
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgH,FrontierSumCleanup1591LowK.kgH,KRegs.m5,Challenge.gateSlots_append,Baselines.rename_gateSlots]
    simp only [ro,ri,rj] at ip a b jp q5 ⊢
    omega
  · have jp := LowZero18Diagonal.make_slots_le (jregsS L ext src dst)
      (jregsS_W L hw ext src dst (by omega) hd he)
    have rj : jregsS L ext src dst=FrontierSumCleanup1591LowK.jregsS L ext src dst := rfl
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgS,FrontierSumCleanup1591LowK.kgS,KRegs.m2,Challenge.gateSlots_append,Baselines.rename_gateSlots]
    simp only [ro,ri,rj] at ip a b jp q2 ⊢
    omega

theorem loan_clear_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18KG.clear (SquareCarryLoan719.patchKG L (kg L ext src dst)))≤
      Challenge.gateSlots (SquareCarryLoan719BF.clear L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have a := (oregs L ext src dst).c8z_slots w
  have b := (oregs L ext src dst).c7y_slots
  have q5 := TrimSquare3.tsq3_slots_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q2 := TrimSquare3.tsq3_slots_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have i1 := LowZero18Diagonal.clearC_slots_old (iregs L ext src dst)
  have jh := LowZero18Diagonal.clear_slots_old (jregsH L ext src dst)
  have js := LowZero18Diagonal.clear_slots_old (jregsS L ext src dst)
  have ro : oregs L ext src dst=FrontierSumCleanup1591LowK.oregs L ext src dst := rfl
  have ri : iregs L ext src dst=FrontierSumCleanup1591LowK.iregs L ext src dst := rfl
  have rh : jregsH L ext src dst=FrontierSumCleanup1591LowK.jregsH L ext src dst := rfl
  have rs : jregsS L ext src dst=FrontierSumCleanup1591LowK.jregsS L ext src dst := rfl
  by_cases h : src.length=128
  all_goals simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,ite_false,LowZero18KG.clear,
    SquareCarryLoan719BF.clear,FrontierSumCleanup1591KG.clear,SquareCarryLoan719.patchKG,
    kgH,kgS,FrontierSumCleanup1591LowK.kgH,FrontierSumCleanup1591LowK.kgS,
    LowZero18Diagonal.clearC,LowZero18Diagonal.clear,KRegs.c5,KRegs.c2,Challenge.gateSlots_append,Baselines.rename_gateSlots]
  all_goals simp only [LowZero18Diagonal.clearC,LowZero18Diagonal.clear,ro,ri,rh,rs] at a b q5 q2 i1 jh js ⊢
  all_goals omega

end ECDSAAdd.Entrant.LowZero18LowK
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareProgram =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18LowK

/-! The checked675/BF719 square with only the18 carry-free low-bit changes. -/
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout

abbrev target := SquareCarryLoan719.target
abbrev earlyHost := SquareCarryLoan719.earlyHost
abbrev earlyPerm := SquareCarryLoan719.earlyPerm
abbrev foldPerm := SquareCarryLoan719.foldPerm
abbrev patchKG := SquareCarryLoan719.patchKG
abbrev K : Nat := ControlLoan1589BFFold.K

def make (L : CuccaroStreamedSquareWideLayout) (R : KG) : Program :=
  LowZero18KG.make (patchKG L R)

def clear (L : CuccaroStreamedSquareWideLayout) (R : KG) : Program :=
  LowZero18KG.clear (patchKG L R)

def clearPrefix (R : KG) : Program :=
  R.R.smk++R.R.c8z++R.R.c7y++R.R.c6++R.Q5c++R.R.scl1591++R.Q2c

def withLowK2 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program) : Program :=
  let R := LowZero18LowK.kg L ext src dst
  copyRegister (some control) src (L.inputBank.take src.length)++make L R++
    eraseMask control src (L.inputBank.take src.length)++
    renameProgram (foldPerm L ext) body++
    copyRegister (some control) src (L.inputBank.take src.length)++clear L R++
    eraseMask control src (L.inputBank.take src.length)

def branchCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagAll12Square.gPrep L++
    withLowK2 L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyC L control)++
    OwnDiagAll12Square.gClear L

def branchBF (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  withLowK2 L ext control L.core.high (L.core.product.take 256) (ControlLoan1589BFFold.bBody L control)

def branchAF (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  withLowK2 L ext control L.core.low (L.core.product.take 256) (ControlLoan1589BFFold.aBody L control)

def reflection (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) : Program :=
  renameProgram (foldPerm L ext) L.reflectOutput

def raw (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  branchCK L ext control++branchBF L ext control++branchAF L ext control++reflection L ext

def fastCandidate (L : ControlledPointLayout) : Program :=
  raw L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def place (L : ControlledPointLayout) (P : Program) : Program :=
  let p0 := renameProgram (Square5Placement.blockPerm L 202) P
  let p1 := renameProgram (OwnPlusSquare.swap L) p0
  let p2 := renameProgram (OwnGuardSquare.swap L) p1
  let p3 := renameProgram (OwnQ4Square.swap L) p2
  let p4 := renameProgram (OwnQ5Square.swap L) p3
  let p5 := renameProgram (OwnDiagAll12PlacedQ6.swap L) p4
  let p6 := renameProgram (OwnDiagAll12PlacedQ7.swap L) p5
  let p7 := renameProgram (PrefixFrontierSquare1591.swap L) p6
  let p8 := renameProgram (Prefix1590Square.swap L) p7
  renameProgram (ControlLoan1589Square.swap L) p8

def program (L : ControlledPointLayout) : Program := place L (fastCandidate L)

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareSupport =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareProgram

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18SquareSupport
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout LowZero18Square
attribute [local irreducible] wires

theorem kg_X1_eq (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    (LowZero18LowK.kg L ext src dst).X1=(OwnDiagLowK.kg L ext src dst).X1 :=
  (LowZero18LowK.kg_metadata L ext src dst).2.1.trans
    (SquareCarryLoan719BFSupport.kg_X1_eq L ext src dst)

section Normal
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

include hw in
theorem target_mem_X1 : target L∈(LowZero18LowK.kg L ext src dst).X1 := by
  rw [(LowZero18LowK.kg_metadata L ext src dst).2.1]
  exact SquareCarryLoan719BFSupport.target_mem_X1 L hw ext src dst

include hw h128 in
theorem earlyHost_mem_outer : earlyHost L∈(LowZero18LowK.kg L ext src dst).R.S := by
  rw [(LowZero18LowK.kg_metadata L ext src dst).1]
  exact SquareCarryLoan719BFSupport.earlyHost_mem_outer L hw ext src dst h128

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem earlyHost_Q1_free :
    earlyHost L∉wires (LowZero18LowK.kg L ext src dst).Q1 ∧
    earlyHost L∉wires (LowZero18LowK.kg L ext src dst).Q1c := by
  have old := SquareCarryLoan719BFSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  exact ⟨fun used=>old.1 (LowZero18LowK.kg_Q1_subset L hw ext src dst h128 hsmax hlen he used),
    fun used=>old.2 (LowZero18LowK.kg_Q1c_subset L ext src dst used)⟩

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem target_clearPrefix_free :
    target L∉wires (LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst)) := by
  have old := SquareCarryLoan719BFSupport.target_clearPrefix_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sub : wires (LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst))⊆
      wires (SquareCarryLoan719BF.clearPrefix (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
    by_cases h : src.length=128
    all_goals simp only [LowZero18Square.clearPrefix,SquareCarryLoan719BF.clearPrefix,
      LowZero18LowK.kg,FrontierSumCleanup1591LowK.kg,h,ite_true,ite_false,
      LowZero18LowK.kgH,LowZero18LowK.kgS,FrontierSumCleanup1591LowK.kgH,FrontierSumCleanup1591LowK.kgS,
      KRegs.c5,KRegs.c2,wires_append]
    all_goals repeat' apply Finset.union_subset_union
    all_goals first | exact (TrimSquare3.tsq3_wires_le _ _ _ _ _).2 | exact LowZero18Diagonal.clear_support_subset _ |
      exact (LowZero18LowK.oregs L ext src dst).c8z_wires w |
      exact (LowZero18LowK.oregs L ext src dst).c7y_wires | exact Finset.Subset.refl _
  exact fun used=>old (sub used)

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem make_tail_free :
    target L∉wires ((LowZero18LowK.kg L ext src dst).Q2++
      (LowZero18LowK.kg L ext src dst).R.smk++(LowZero18LowK.kg L ext src dst).Q5++
      (LowZero18LowK.kg L ext src dst).R.m6++(LowZero18LowK.kg L ext src dst).R.m7y++
      (LowZero18LowK.kg L ext src dst).R.m8z++(LowZero18LowK.kg L ext src dst).R.scl1591) := by
  have old := SquareCarryLoan719BFSupport.make_tail_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sub : wires ((LowZero18LowK.kg L ext src dst).Q2++
      (LowZero18LowK.kg L ext src dst).R.smk++(LowZero18LowK.kg L ext src dst).Q5++
      (LowZero18LowK.kg L ext src dst).R.m6++(LowZero18LowK.kg L ext src dst).R.m7y++
      (LowZero18LowK.kg L ext src dst).R.m8z++(LowZero18LowK.kg L ext src dst).R.scl1591)⊆
    wires ((FrontierSumCleanup1591LowK.kg L ext src dst).Q2++
      (FrontierSumCleanup1591LowK.kg L ext src dst).R.smk++(FrontierSumCleanup1591LowK.kg L ext src dst).Q5++
      (FrontierSumCleanup1591LowK.kg L ext src dst).R.m6++(FrontierSumCleanup1591LowK.kg L ext src dst).R.m7++
      (FrontierSumCleanup1591LowK.kg L ext src dst).R.m8++(FrontierSumCleanup1591LowK.kg L ext src dst).R.scl1591) := by
    by_cases h : src.length=128
    · have jp := LowZero18Diagonal.make_support_subset (LowZero18LowK.jregsH L ext src dst)
        (LowZero18LowK.jregsH_W L hw ext src dst h hlen he)
      simp only [LowZero18LowK.kg,FrontierSumCleanup1591LowK.kg,h,ite_true,
        LowZero18LowK.kgH,FrontierSumCleanup1591LowK.kgH,KRegs.m5,wires_append]
      repeat' apply Finset.union_subset_union
      all_goals first | exact jp | exact (TrimSquare3.tsq3_wires_le _ _ _ _ _).1 | exact (LowZero18LowK.oregs L ext src dst).m7y_wires |
        exact (LowZero18LowK.oregs L ext src dst).m8z_wires w | exact Finset.Subset.refl _
    · have jp := LowZero18Diagonal.make_support_subset (LowZero18LowK.jregsS L ext src dst)
        (LowZero18LowK.jregsS_W L hw ext src dst (by omega) hlen he)
      simp only [LowZero18LowK.kg,FrontierSumCleanup1591LowK.kg,h,ite_false,
        LowZero18LowK.kgS,FrontierSumCleanup1591LowK.kgS,KRegs.m2,wires_append]
      repeat' apply Finset.union_subset_union
      all_goals first | exact jp | exact (TrimSquare3.tsq3_wires_le _ _ _ _ _).1 | exact (LowZero18LowK.oregs L ext src dst).m7y_wires |
        exact (LowZero18LowK.oregs L ext src dst).m8z_wires w | exact Finset.Subset.refl _
  exact fun used=>old (sub used)

end Normal
end ECDSAAdd.Entrant.LowZero18SquareSupport
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareHandoff =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareSupport

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] run wires

abbrev fold_run_eq := SquareCarryLoan719.fold_run_eq

theorem patchKG_make_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (K : KG)
    (sp : K.Spec) (targetX1 : target L∈K.X1) (hostS : earlyHost L∈K.R.S)
    (hostFree : earlyHost L∉wires K.Q1)
    (innerZero : ∀v t,K.I1 v t → t (target L)=false) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=0) (hS0 : regValue K.R.S s.basis=0)
    (hX0 : regValue K.X s.basis=0) (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    run (LowZero18Square.make L K) m s=run (LowZero18KG.make K) m s := by
  have dlo0 : regValue K.R.dlo s.basis=0 := (regValue_zero _ _).mpr (fun q hq =>
    (regValue_zero _ _).mp hd0 q (List.mem_of_mem_take hq))
  have x10 : regValue K.X1 s.basis=0 := (regValue_zero _ _).mpr (fun q hq =>
    (regValue_zero _ _).mp hX0 q (by simp only [KG.X,List.mem_append];tauto))
  have headEq (records : List Bool) := SquareCarryLoan719.q1_run_eq L hw K sp targetX1 hostFree innerZero
    s records dlo0 x10 hp0 hc0 hz0 hi0 ((regValue_zero _ _).mp hS0 _ hostS)
  let tail := K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7y++K.R.m8z++K.R.scl1591
  have oldShape : LowZero18KG.make K=K.Q1++tail := by simp only [LowZero18KG.make,tail,List.append_assoc]
  have newShape : LowZero18Square.make L K=renameProgram (earlyPerm L) K.Q1++tail := by
    simp only [LowZero18Square.make,SquareCarryLoan719.patchKG,LowZero18KG.make,tail,List.append_assoc]
  simp only [newShape,oldShape,run_append,(renameProgram_counts _ _).2]
  rw [headEq]

theorem make_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
    (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (sp : (LowZero18LowK.kg L ext src dst).Spec) (s : State) (m : List Bool)
    (hd0 : regValue (LowZero18LowK.kg L ext src dst).R.dst s.basis=0)
    (hS0 : regValue (LowZero18LowK.kg L ext src dst).R.S s.basis=0)
    (hX0 : regValue (LowZero18LowK.kg L ext src dst).X s.basis=0)
    (hz0 : regValue (LowZero18LowK.kg L ext src dst).R.z s.basis=0)
    (hp0 : regValue (LowZero18LowK.kg L ext src dst).R.pad s.basis=0)
    (hc0 : regValue (LowZero18LowK.kg L ext src dst).R.carry s.basis=0)
    (hi0 : s.basis (LowZero18LowK.kg L ext src dst).R.cin=false) :
    run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) m s=
      run (LowZero18KG.make (LowZero18LowK.kg L ext src dst)) m s := by
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  apply patchKG_make_run_eq L hw (LowZero18LowK.kg L ext src dst) sp
    (LowZero18SquareSupport.target_mem_X1 L hw ext src dst)
    (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128) free.1
    ?_ s m hd0 hS0 hX0 hz0 hp0 hc0 hi0
  intro v t inv
  rw [LowZero18LowK.kg_I1] at inv
  exact (regValue_zero _ _).mp inv.1 _
    (SquareCarryLoan719Support.target_mem_inner L hw ext src dst)

theorem clear_run_eq_of_boundaries (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (K : KG) (s : State) (m : List Bool)
    (prefixFree : target L∉wires (clearPrefix K))
    (hostFree : earlyHost L∉wires K.Q1c)
    (targetIn : s.basis (target L)=false)
    (targetOut : (run (LowZero18KG.clear K) m s).basis (target L)=false)
    (hostOut : (run (LowZero18KG.clear K) m s).basis (earlyHost L)=false) :
    run (LowZero18Square.clear L K) m s=run (LowZero18KG.clear K) m s := by
  let middle := run (clearPrefix K) (m.take (measurementCount (clearPrefix K))) s
  let records := m.drop (measurementCount (clearPrefix K))
  have oldShape : LowZero18KG.clear K=clearPrefix K++K.Q1c := by
    simp only [LowZero18KG.clear,LowZero18Square.clearPrefix,List.append_assoc]
  have newShape : LowZero18Square.clear L K=clearPrefix K++renameProgram (earlyPerm L) K.Q1c := by
    simp only [LowZero18Square.clear,SquareCarryLoan719.patchKG,LowZero18KG.clear,LowZero18Square.clearPrefix,List.append_assoc]
  have oldRun : run (LowZero18KG.clear K) m s=run K.Q1c records middle := by rw [oldShape,run_append]
  have targetMid : middle.basis (target L)=false :=
    (run_preserves_outside _ _ s _ prefixFree).trans targetIn
  rw [oldRun] at targetOut hostOut
  have hostMid : middle.basis (earlyHost L)=false :=
    (run_preserves_outside _ records middle _ hostFree).symm.trans hostOut
  have lastEq := NewFieldFrameOB5.rebind_swap_run (target L) (earlyHost L) K.Q1c
    middle records targetMid hostMid targetOut hostOut
  rw [←SquareCarryLoan719.earlyPerm_eq L hw] at lastEq
  rw [newShape,oldShape,run_append,run_append]
  exact lastEq

theorem cross_host_zero (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire)
    (h128 : 128≤src.length) (he : 300≤ext.length) (s : BasisState) (a b : Nat)
    (value : regValue (LowZero18LowK.oregs L ext src dst).T s=2*a*b) :
    s (ext.getD 0 0)=false :=
  SquareCarryLoan719.cross_host_zero L ext src dst h128 he s a b value

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareProof =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareHandoff

/-! The checked BF719 state proof with only the LowZero producer/cleanup constructors changed. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

private theorem k2_xor_false_eq {a b : Bool} (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem withLowK2_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hbody : ∀q∈ext,q∉ECDSAAdd.wires body)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (LowZero18Square.withLowK2 L ext control src dst body) records s).phase=s.phase ∧
    regValue L.core.out (run (LowZero18Square.withLowK2 L ext control src dst body) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (LowZero18Square.withLowK2 L ext control src dst body) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈LowZero18LowK.ktmp L,q∉L.core.out := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈LowZero18LowK.ktmp L,q∉dst := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈LowZero18LowK.ktmp L,q∉src := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈LowZero18LowK.ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈LowZero18LowK.ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉LowZero18LowK.ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉LowZero18LowK.ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlD : control∉dst := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlE : control∉ext := fun h => hdx control h (by simp)
  have ctlO : control∉L.core.out := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have srcB : ∀q∈src,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcD : ∀q∈src,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcOut : ∀q∈src,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bOut : ∀q∈(L.inputBank.take src.length),q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have dOut : ∀q∈dst,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padOut : ∀q∈L.leafPad,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carOut : ∀q∈L.leafCarry,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinOut : L.core.cin∉L.core.out := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padD : ∀q∈L.leafPad,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carD : ∀q∈L.leafCarry,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinD : L.core.cin∉dst := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padE : ∀q∈L.leafPad,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carE : ∀q∈L.leafCarry,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinE : L.core.cin∉ext := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  -- generic "not a leaf scratch wire" from being outside ext and LowZero18LowK.ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉LowZero18LowK.ktmp L) :
      q∉(LowZero18LowK.oregs L ext src dst).dst ∧ q∉(LowZero18LowK.oregs L ext src dst).T ∧ q∉(LowZero18LowK.kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  let P := if s.basis control then regValue src s.basis else 0
  obtain ⟨a6,r7,e7⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body++
    copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.clear L (LowZero18LowK.kg L ext src dst))) (eraseMask control src (L.inputBank.take src.length)) records s
  obtain ⟨a5,r6,e6⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body++
    copyRegister (some control) src (L.inputBank.take src.length)) (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body)
    (copyRegister (some control) src (L.inputBank.take src.length)) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)) (renameProgram (foldPerm L ext) body) a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))) (eraseMask control src (L.inputBank.take src.length)) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)) (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) a2 s
  rw [show LowZero18Square.withLowK2 L ext control src dst body=copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body++copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.clear L (LowZero18LowK.kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length) from rfl,e7,e6,e5,e4,e3,e2]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have mkEq := make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  simp only [←mkEq] at mk
  have i1 := mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at i1
  rw [hKR] at mk
  generalize run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2 u0=u1 at mk i1 ⊢
  have u1s : ∀q,q∉(LowZero18LowK.oregs L ext src dst).dst → q∉(LowZero18LowK.oregs L ext src dst).T → q∉(LowZero18LowK.kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈LowZero18LowK.ktmp L
    · by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · have hI : q∈((LowZero18LowK.ktmp L).drop 66).take 33 := (LowZero18LowK.kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
        rw [(regValue_zero _ _).mp i1.1 q hI,u0s q (tmpB q hT),tmp0 q hT]
      · exact u1s q hD (fun h => hE (xT q h)) hX
    · exact u1s q hD (fun h => hE (xT q h)) (fun h => (xX q h).elim hE hT)
  have bank1 : regValue (L.inputBank.take src.length) u1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => u1z q (bD q hq) (fun h => extB q h hq))).trans bank0
  have src1 : regValue src u1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq)))
  have ctl1 : u1.basis control=s.basis control := (u1z _ ctlD ctlE).trans (u0s _ ctlB)
  have dst1 : regValue dst u1.basis=P^2 := by rw [←bank0]; exact mk.2.1
  -- erase
  obtain ⟨ep1,ef1,ev1⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask u1 r3 (by
    rw [bank1,ctl1,src1])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r3 u1=u2 at ep1 ef1 ev1 ⊢
  have u2s : ∀q,q∉dst → q∉ext → u2.basis q=s.basis q := by
    intro q hq hx
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev1 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · exact (ef1 q hb).trans ((u1z q hq hx).trans (u0s q hb))
  have u2ext : ∀q∈ext,u2.basis q=u1.basis q := fun q h => ef1 q (extB q h)
  -- body
  let u2' : State := ⟨u2.phase,fun q => if q∈ext then s.basis q else u2.basis q⟩
  have dst2' : regValue dst u2'.basis=P^2 := by
    rw [←dst1]
    apply regValue_congr
    intro q hq
    have hx : q∉ext := fun h => extD q h hq
    simp only [u2',hx,if_false]
    exact ef1 q (fun h => bD q h hq)
  have cb := callback u2' r4 dst2' (by
    intro q hq
    by_cases hx : q∈ext
    · simp only [u2',hx,if_true]
    · simp only [u2',hx,if_false]; exact u2s q hq hx)
  have loc := run_local_increment body u2 u2' r4 (by
    intro q hq
    have hx : q∉ext := fun h => hbody q h hq
    simp only [u2',hx,if_false])
  generalize hv' : run body r4 u2'=v' at cb loc
  generalize hv : run body r4 u2=v at loc
  have vIn : ∀q∈ext,v.basis q=u2.basis q := by
    intro q hq; rw [←hv]; exact run_preserves_outside body r4 u2 q (hbody q hq)
  have vOut : ∀q,q∉ext → v.basis q=v'.basis q := by
    intro q hq
    by_cases hb : q∈ECDSAAdd.wires body
    · exact loc.2 q hb
    · rw [←hv,←hv',run_preserves_outside body r4 u2 q hb,run_preserves_outside body r4 u2' q hb]
      simp only [u2',hq,if_false]
  have vPhase : v.phase=u2.phase := by
    apply k2_xor_false_eq
    rw [loc.1,cb.1]
    cases u2'.phase <;> rfl
  have vFrame : ∀q,q∉L.core.out → v.basis q=u2.basis q := by
    intro q hq
    by_cases hx : q∈ext
    · exact vIn q hx
    · rw [vOut q hx,cb.2.2 q hq]; simp only [u2',hx,if_false]
  have vVal : regValue L.core.out v.basis=V :=
    (regValue_congr _ _ _ (fun q hq => vOut q (fun h => extOut q h hq))).trans cb.2.1
  have targetTmp : target L∈LowZero18LowK.ktmp L := by
    apply DiagSq.getD_in
    rw [LowZero18LowK.ktmp_length L hw]
    omega
  have targetIn : u2.basis (target L)=false :=
    (u2s _ (tmpD _ targetTmp) (tmpE _ targetTmp)).trans (tmp0 _ targetTmp)
  have targetOut : (run body r4 u2).basis (target L)=false := by
    rw [hv]
    exact (vFrame _ (tmpOut _ targetTmp)).trans targetIn
  have extMember : ext.getD 0 0∈ext := DiagSq.getD_in _ 0 (by omega)
  have hostIn : u2.basis (ext.getD 0 0)=false :=
    (u2ext _ extMember).trans
      (cross_host_zero L ext src dst h128 he u1.basis _ _ mk.2.2.2.1)
  have foldEq := fold_run_eq L hw ext body u2 r4 targetIn targetOut hostIn (hbody _ extMember)
  rw [hv] at foldEq
  rw [foldEq]
  -- second copy
  obtain ⟨cp2,cf2,cv2⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB v r5
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r5 v=w0 at cp2 cf2 cv2 ⊢
  have vB : ∀q∈(L.inputBank.take src.length),v.basis q=s.basis q := fun q hq =>
    (vFrame q (bOut q hq)).trans (u2s q (bD q hq) (fun h => extB q h hq))
  have vSrc : ∀q∈src,v.basis q=s.basis q := fun q hq =>
    (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq))
  have bankW : regValue (L.inputBank.take src.length) w0.basis=P := by
    rw [cv2,show regValue (L.inputBank.take src.length) v.basis=0 from (regValue_congr _ _ _ vB).trans banks.1,Nat.zero_xor]
    change (if v.basis control then regValue src v.basis else 0)=P
    rw [show v.basis control=s.basis control from (vFrame _ ctlO).trans (u2s _ ctlD ctlE),regValue_congr _ _ _ vSrc]
  have w0u1 : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → w0.basis q=u1.basis q := by
    intro q hb ho
    rw [cf2 q hb,vFrame q ho]
    by_cases hx : q∈ext
    · exact u2ext q hx
    · exact ef1 q hb
  have w0s : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → q∉dst → q∉ext → w0.basis q=s.basis q :=
    fun q hb ho hD hE => (w0u1 q hb ho).trans ((u1z q hD hE).trans (u0s q hb))
  have bankLoHi : regValue (LowZero18LowK.oregs L ext src dst).lo w0.basis=regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis ∧
      regValue (LowZero18LowK.oregs L ext src dst).hi w0.basis=regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis := by
    have l1 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) w0.basis
    have l2 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) u0.basis
    have h1 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) w0.basis
    have h2 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) u0.basis
    rw [bankW] at l1 h1
    rw [bank0] at l2 h2
    exact ⟨l1.trans l2.symm,h1.trans h2.symm⟩
  have xE (q : Wire) (h : q∈ext ∨ q∈LowZero18LowK.ktmp L) : q∉(L.inputBank.take src.length) ∧ q∉L.core.out :=
    h.elim (fun e => ⟨extB q e,extOut q e⟩) (fun e => ⟨tmpB q e,tmpOut q e⟩)
  have Xw : ∀q∈(LowZero18LowK.kg L ext src dst).X,w0.basis q=u1.basis q := fun q h =>
    w0u1 q (xE q (xX q h)).1 (xE q (xX q h)).2
  have X1w : ∀q∈(LowZero18LowK.kg L ext src dst).X1,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X2w : ∀q∈(LowZero18LowK.kg L ext src dst).X2,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X5w : ∀q∈(LowZero18LowK.kg L ext src dst).X5,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have carW : regValue L.leafCarry w0.basis=0 :=
    ((regValue_congr _ _ _ (fun q hq => w0s q (carB q hq) (carOut q hq) (carD q hq) (carE q hq)))).trans banks.2.2
  have I1w := sp.lc1 _ u1.basis w0.basis X1w mk.2.2.2.2.1
  have I2w := sp.lc2 _ u1.basis w0.basis X2w mk.2.2.2.2.2.1
  have I5w := sp.lc5 _ u1.basis w0.basis X5w mk.2.2.2.2.2.2.1
  rw [←bankLoHi.1] at I1w
  rw [←bankLoHi.2] at I2w
  rw [←bankLoHi.1,←bankLoHi.2] at I5w
  have cl := LowZero18KG.clear_correct (LowZero18LowK.kg L ext src dst) sp hall w0 r6
    (by
      rw [hKR,show regValue (LowZero18LowK.oregs L ext src dst).bank w0.basis=P from bankW,
        show regValue (LowZero18LowK.oregs L ext src dst).dst w0.basis=regValue (LowZero18LowK.oregs L ext src dst).dst u1.basis from
          regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => bD q h hq) (fun h => dOut q hq h))]
      exact dst1)
    (by
      rw [hKR,←mk.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (tmpB q (xS q hq)) (tmpOut q (xS q hq))))
    (by
      rw [hKR,bankLoHi.1,bankLoHi.2,←mk.2.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => extB q (xT q hq) h)
        (fun h => extOut q (xT q hq) h)))
    (by rw [hKR]; exact I1w) (by rw [hKR]; exact I2w) (by rw [hKR]; exact I5w)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (xz q hq)))
    (by rw [hKR]; exact (regValue_congr _ _ _ (fun q hq => w0s q (padB q hq) (padOut q hq) (padD q hq) (padE q hq))).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (List.mem_of_mem_take hq)))
    (by rw [hKR]; exact (w0s _ cinB cinOut cinD cinE).trans hc.cin)
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have clEq := clear_run_eq_of_boundaries L hw (LowZero18LowK.kg L ext src dst) w0 r6
    (LowZero18SquareSupport.target_clearPrefix_free
      L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he) free.2
    (by
      have inv := I1w
      rw [LowZero18LowK.kg_I1] at inv
      exact (regValue_zero _ _).mp inv.1 _
        (SquareCarryLoan719Support.target_mem_inner L hw ext src dst))
    ((regValue_zero _ _).mp cl.2.2.2.2.1 _ (by
      have member := LowZero18SquareSupport.target_mem_X1 L hw ext src dst
      simp only [KG.X,List.mem_append]
      tauto))
    ((regValue_zero _ _).mp cl.2.2.1 _
      (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128))
  simp only [←clEq] at cl
  rw [hKR] at cl
  generalize run (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) r6 w0=w1 at cl ⊢
  have w1s : ∀q,q∉dst → q∉ext → q∉LowZero18LowK.ktmp L → w1.basis q=w0.basis q := fun q hD hE hT =>
    let o := nK q hD hE hT; cl.2.2.2.2.2 q o.1 o.2.1 o.2.2
  have w1B : regValue (L.inputBank.take src.length) w1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => w1s q (bD q hq) (fun h => extB q h hq) (fun h => tmpB q h hq))).trans bankW
  have w1src : regValue src w1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (w1s q (srcD q hq) (fun h => extSrc q h hq) (fun h => tmpSrc q h hq)).trans
      ((cf2 q (srcB q hq)).trans (vSrc q hq)))
  have w1ctl : w1.basis control=s.basis control :=
    (w1s _ ctlD ctlE ctlT).trans ((cf2 _ ctlB).trans ((vFrame _ ctlO).trans (u2s _ ctlD ctlE)))
  obtain ⟨ep2,ef2,ev2⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask w1 r7 (by
    rw [w1B,w1ctl,w1src])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r7 w1=w2 at ep2 ef2 ev2 ⊢
  refine ⟨ep2.trans (cl.1.trans (cp2.trans (vPhase.trans (ep1.trans (mk.1.trans cp1))))),?_,?_⟩
  · rw [←vVal]
    apply regValue_congr
    intro q hq
    have o := nK q (fun h => dOut q h hq) (fun h => extOut q h hq) (fun h => tmpOut q h hq)
    rw [ef2 q (fun h => bOut q h hq),cl.2.2.2.2.2 q o.1 o.2.1 o.2.2,cf2 q (fun h => bOut q h hq)]
  · intro q hq
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev2 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [ef2 q hb]
      by_cases hD : q∈(LowZero18LowK.oregs L ext src dst).dst
      · exact ((regValue_zero _ _).mp cl.2.1 q hD).trans ((regValue_zero _ _).mp hzero q hD).symm
      by_cases hT : q∈(LowZero18LowK.oregs L ext src dst).T
      · exact ((regValue_zero _ _).mp cl.2.2.2.1 q hT).trans (ext0 q (xT q hT)).symm
      by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · rw [(regValue_zero _ _).mp cl.2.2.2.2.1 q hX]
        rcases xX q hX with e|e
        · exact (ext0 q e).symm
        · exact (tmp0 q e).symm
      rw [cl.2.2.2.2.2 q hD hT hX,cf2 q hb,vFrame q hq]
      by_cases hx : q∈ext
      · rw [u2ext q hx,u1s q hD hT hX,u0s q hb]
      · exact u2s q hD hx


theorem reflection_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (ext : List Wire)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (O : Nat) (hO : O<SquareReduction.p)
    (s : State) (m : List Bool) (ho : regValue L.core.out s.basis=O)
    (hc : L.PairClean s.basis) (hz : regValue ext s.basis=0) :
    (run (reflection L ext) m s).phase=s.phase ∧
    regValue L.core.out (run (reflection L ext) m s).basis=SquareReduction.p-1-O ∧
    ∀q,q∉L.core.out → (run (reflection L ext) m s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have old := L.reflectOutput_correct hw nd O hO s m ho hc
  have len := OwnDiagLowK.ktmp_length L hw
  have member : target L∈OwnDiagLowK.ktmp L := DiagSq.getD_in _ 67 (by omega)
  have pad : target L∈L.foldPad := List.mem_of_mem_drop member
  have away : target L∉L.core.out :=
    (L.pairAuxAway nd _ (by simp only [List.mem_append];tauto)).2
  have tin : s.basis (target L)=false := (regValue_zero _ _).mp hc.pad _ pad
  have tout : (run L.reflectOutput m s).basis (target L)=false := (old.2.2 _ away).trans tin
  have host : ext.getD 0 0∈ext := DiagSq.getD_in _ 0 (by have h:=he.len;omega)
  have hin : s.basis (ext.getD 0 0)=false := (regValue_zero _ _).mp hz _ host
  have free : ext.getD 0 0∉wires L.reflectOutput := fun used=>
    he.away _ host (List.mem_toFinset.mp (ControlLoan1589BFFold.reflect_support L control used))
  have eq := SquareCarryLoan719.fold_run_eq L hw ext L.reflectOutput s m tin tout hin free
  simpa only [reflection,eq] using old

def middleCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.withLowK2 L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyC L control)

theorem middleCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (middleCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (middleCK L ext control) records s).basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (middleCK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (OwnDiagAll12Square.bodyC L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (OwnDiagAll12Square.bodyC_support L hw nd control hw'))
  apply LowZero18Square.withLowK2_correct L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
    (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) ext he.nodup he.away he.len (OwnDiagAll12Square.bodyC L control) hbody
    s records hc hp0 hz
  intro t m dstValue same
  have ctrlT : t.basis control=s.basis control :=
    same control (fun h => (List.nodup_cons.mp hn).1
      (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]))
  have pv : regValue L.core.product t.basis=M^2 := by simpa [M,hs] using dstValue
  have clean := L.measured_product_frame_clean nd L.core.product (fun _ => le_rfl) s.basis t.basis hc same
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q
      (fun hp => List.disjoint_left.mp (L.product_out_disjoint nd) hp hq))).trans ho
  have r := OwnDiagAll12Square.accMiddleCF_body L hw control hn M O hO t m pv
    (by intro h; rw [ctrlT] at h; simp [M,h]) clean outO
  rw [ctrlT] at r
  exact r

theorem branchCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (LowZero18Square.branchCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (LowZero18Square.branchCK L ext control) records s).basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (LowZero18Square.branchCK L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  have ctrlAway : control∉L.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp hn control
    have pos := List.count_pos_iff.mpr bad
    have sumBound := L.measured_sum_count control
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h sumBound
    omega
  let middle := middleCK L ext control
  let mp := measurementCount (OwnDiagAll12Square.gPrep L)
  let rest := records.drop mp
  let u := run (OwnDiagAll12Square.gPrep L) (records.take mp) s
  let v := run middle (rest.take (measurementCount middle)) u
  let out := run (OwnDiagAll12Square.gClear L) (rest.drop (measurementCount middle)) v
  have prep := OwnDiagAll12Square.gPrep_frame L hw nd s.basis A B ha bound (PairClean.corePad L s.basis hc) hc.cin hc.work
    s (records.take mp) (show SquareFrame L.core.sum s.basis B s.basis from ⟨hb,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))).trans ho
  have ctrlU : u.basis control=s.basis control := prep.2.2 control ctrlAway
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have hzU : regValue ext u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => he.away q hq (OwnDiagAll12Square.sum_in L control q bad)))).trans hz
  have used := middleCK_correct L hw ext control hn (A+B) O hO u
    (rest.take (measurementCount middle)) prep.2.1 outU productU cleanU he hzU
  rw [ctrlU] at used
  let restoreBase : BasisState := fun q => if q∈L.core.out then v.basis q else s.basis q
  have lowOutAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have lowRestore : regValue L.core.low restoreBase=A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) ha
    intro q hq
    simp [restoreBase,lowOutAway q hq]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    simp [restoreBase,List.disjoint_left.mp dis.2 hq]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (PairClean.corePad L s.basis hc)
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad,hq])).2
    simp [restoreBase,away]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway nd L.core.cin (by simp)).2
    simp [restoreBase,away,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans prep.2.1
    · intro q hq
      by_cases outSite : q∈L.core.out
      · simp [restoreBase,outSite]
      · simp only [restoreBase,if_neg outSite]
        exact (used.2.2 q outSite).trans (prep.2.2 q hq)
  have workRestore : regValue L.core.work restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hc.work
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [hq])).2
    simp [restoreBase,away]
  have cleared := OwnDiagAll12Square.gClear_frame L hw nd restoreBase A B lowRestore bound padRestore cinRestore workRestore
    v (rest.drop (measurementCount middle)) clearPre
  have finalValue : regValue L.core.out out.basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O := by
    apply Eq.trans (regValue_congr _ _ _ ?_) used.2.1
    intro q hq
    have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
    simpa [restoreBase,hq] using same
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨cleared.1.trans (used.1.trans prep.1),finalValue,?_⟩
    intro q hq
    by_cases sumSite : q∈L.core.sum
    · exact (regValue_eq_iff L.core.sum out.basis s.basis).mp (cleared.2.1.trans hb.symm) q sumSite
    · have same := cleared.2.2 q sumSite
      simpa [restoreBase,hq] using same
  simpa [LowZero18Square.branchCK,middleCK,middle,u,v,out,rest,mp,run_append] using final


theorem branchBF_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (branchBF L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (branchBF L ext control) records s).basis=
      ControlLoan1589BFFold.resBF ((if s.basis control then B else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (branchBF L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (ControlLoan1589BFFold.bBody L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (ControlLoan1589BFFold.bBody_support L hw nd control hw'))
  apply LowZero18Square.withLowK2_correct L hw control hn L.core.high (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) ext he.nodup he.away he.len
    (ControlLoan1589BFFold.bBody L control) hbody s records hc dstZero hz
  intro t m dstValue same
  rw [hb] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have frame := ControlLoan1589BFFold.bBody_frame L hw nd control hcw t.basis M mb full clean O hO t m ⟨outO,fun _ _ => rfl⟩
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  rw [ControlLoan1589BFFold.bO4_eq M O (t.basis control) mb hg hO,ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩

theorem branchAF_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (branchAF L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (branchAF L ext control) records s).basis=
      ControlLoan1589BFFold.resAF ((if s.basis control then A else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (branchAF L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (ControlLoan1589BFFold.aBody L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (ControlLoan1589BFFold.aBody_support L hw nd control hw'))
  apply LowZero18Square.withLowK2_correct L hw control hn L.core.low (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) ext he.nodup he.away he.len
    (ControlLoan1589BFFold.aBody L control) hbody s records hc dstZero hz
  intro t m dstValue same
  rw [ha] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  have frame := ControlLoan1589BFFold.aBody_frame L hw nd control hcw t.basis M mb full clean O hO hg t m ⟨outO,fun _ _ => rfl⟩
  rw [ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩


theorem raw_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (raw L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (raw L ext control) records s).basis=
      ((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (raw L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := ControlLoan1589BFFold.resAF PA OB enabled
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have low (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.low t=A := regValue_congr _ _ _ (fun q hq => hf.2 q (lowAway q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.high t=B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.sum t=B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.product t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue ext t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (LowZero18Square.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := LowZero18Square.branchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OB hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepR : Triple (SquareFrame L.core.out s.basis OA) (reflection L ext)
      (SquareFrame L.core.out s.basis (SquareReduction.p-1-OA)) := by
    intro t m hf
    have h := reflection_correct L hw control hn ext he OA (ofCast_lt _ _) t m hf.1
      (L.squareFrame_clean nd s.basis t.basis OA hf hc) (extZ _ _ hf)
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := ((stepC.seq stepB).seq stepA).seq stepR
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := ControlLoan1589BFFold.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  exact ⟨phase,value.trans exactResult,frame⟩


theorem raw_state_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (m mOld : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) (he : ECDSAAdd.Entrant.ExtOK L control ext)
    (hz : regValue ext s.basis=0) :
    run (raw L ext control) m s=run (ControlLoan1589BFFold.program L ext control) mOld s := by
  have fresh := raw_correct L hw ext control hn Y O hO s m hy ho hp0 hs0 hc he hz
  have prior := ControlLoan1589BFFold.correct L hw ext control hn Y O hO s mOld hy ho hp0 hs0 hc he hz
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · funext q
    by_cases inside : q∈L.core.out
    · exact (regValue_eq_iff _ _ _).mp (fresh.2.1.trans prior.2.1.symm) q inside
    · exact (fresh.2.2 q inside).trans (prior.2.2 q inside).symm

open Secp256k1 MappedCompressed CompressedPointDialog

theorem fastCandidate_state_eq (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (hX : X<p) (s : State) (m mOld : List Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    run (fastCandidate L) m s=run (ControlLoan1589BFSquare.fastCandidate L) mOld s := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := raw_state_eq K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m mOld hy hx prod0 sum0 clean
    (ECDSAAdd.Entrant.kext_ok L hw hn) hz
  simpa only [fastCandidate,ControlLoan1589BFSquare.fastCandidate] using kernel

theorem candidate_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ControlLoan1589BFSquare.SquareCorrectK L K (fastCandidate L) := by
  intro X Y G origin s m v
  have old := ControlLoan1589BFSquare.candidate_correct L hw hn X Y G origin s m v
  have eq := fastCandidate_state_eq L hw hn X.val Y.val X.isLt s m m v.x v.y v.clean
  simpa only [eq] using old

private theorem relabel (L : ControlledPointLayout) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool) (hf : ∀q,q∉L.dialogPool → e q=q)
    (P : Program) (old : ControlLoan1589BFSquare.SquareCorrectK L K P) :
    ControlLoan1589BFSquare.SquareCorrectK L K (renameProgram e P) := by
  intro X Y G origin s m v
  have result := old X Y G origin s m v
  have eq := Square5Placement.pool_relabel_state_eq L e hp hf P s m v.clean result.2.clean
  simpa only [eq] using result

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ControlLoan1589BFSquare.SquareCorrectK L K (program L) := by
  have a0 := relabel L (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) _ (candidate_correct L hw hn)
  have a1 := relabel L (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw) (OwnPlusSquare.outside L hw) _ a0
  have a2 := relabel L (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw) (OwnGuardSquare.outside L hw) _ a1
  have a3 := relabel L (OwnQ4Square.swap L) (OwnQ4Square.pool L hw) (OwnQ4Square.outside L hw) _ a2
  have a4 := relabel L (OwnQ5Square.swap L) (OwnQ5Square.pool L hw) (OwnQ5Square.outside L hw) _ a3
  have a5 := relabel L (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.pool L hw) (OwnDiagAll12PlacedQ6.outside L hw) _ a4
  have a6 := relabel L (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.pool L hw) (OwnDiagAll12PlacedQ7.outside L hw) _ a5
  have a7 := relabel L (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.pool L hw) (PrefixFrontierSquare1591.outside L hw) _ a6
  have a8 := relabel L (Prefix1590Square.swap L) (Prefix1590Square.pool L hw) (Prefix1590Square.outside L hw) _ a7
  have a9 := relabel L (ControlLoan1589Square.swap L) (ControlLoan1589Square.pool L hw) (ControlLoan1589Square.outside L hw) _ a8
  exact a9

theorem step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (K:Fp) else 0)) Y G origin) :=
  correct L hw hn X Y G origin

private theorem values_unique {L : ControlledPointLayout} {X Y : Fp} {G : Bool}
    {origin a b : BasisState} (ha : PointDialogValues L X Y G origin a)
    (hb : PointDialogValues L X Y G origin b) : a=b := by
  funext q
  by_cases hx : q∈L.point.x
  · exact (regValue_eq_iff _ _ _).mp (ha.x.trans hb.x.symm) q hx
  · by_cases hy : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp (ha.y.trans hb.y.symm) q hy
    · have away : q∉L.point.x++L.point.y := by
        simpa only [List.mem_append,not_or] using And.intro hx hy
      exact (ha.rest q away).trans (hb.rest q away).symm

theorem state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) m s=run (ControlLoan1589BFSquare.program L) mOld s := by
  have fresh := correct L hw hn X Y G origin s m v
  have prior := ControlLoan1589BFSquare.correct L hw hn X Y G origin s mOld v
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · exact values_unique fresh.2 prior.2

theorem cleanup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    regValue L.dialogPool (run (program L) m s).basis=0 :=
  (correct L hw hn X Y G origin s m v).2.clean

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareResources =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareProof

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] wires toffoliCount measurementCount Challenge.gateSlots

private theorem source_counts (L : CuccaroStreamedSquareWideLayout) :
    (∀q,L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q) ∧
    (∀q,L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q) ∧
    (∀q,L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q) ∧
    (∀q,(L.core.product.take 256).count q≤L.core.product.count q) := by
  have hh (q : Wire) : L.core.high.count q≤L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans ((List.drop_sublist 128 L.core.y).count_le q)
  refine ⟨?_,?_,?_,fun q=>(List.take_sublist 256 L.core.product).count_le q⟩
  · intro q
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢;omega
  · intro q;have h := hh q;simp only [List.count_append];omega
  · intro q;have h := hh q;simp only [CuccaroStreamedSquareLayout.sum,List.count_append];omega

theorem patchKG_counts (L : CuccaroStreamedSquareWideLayout) (R : KG) :
    toffoliCount (LowZero18Square.make L R)=toffoliCount (LowZero18KG.make R) ∧
    measurementCount (LowZero18Square.make L R)=measurementCount (LowZero18KG.make R) ∧
    toffoliCount (LowZero18Square.clear L R)=toffoliCount (LowZero18KG.clear R) ∧
    measurementCount (LowZero18Square.clear L R)=measurementCount (LowZero18KG.clear R) := by
  simp only [LowZero18Square.make,LowZero18Square.clear,SquareCarryLoan719.patchKG,
    LowZero18KG.make,LowZero18KG.clear,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,and_self]

theorem patchKG_slots (L : CuccaroStreamedSquareWideLayout) (R : KG) :
    Challenge.gateSlots (LowZero18Square.make L R)=Challenge.gateSlots (LowZero18KG.make R) ∧
    Challenge.gateSlots (LowZero18Square.clear L R)=Challenge.gateSlots (LowZero18KG.clear R) := by
  simp only [LowZero18Square.make,LowZero18Square.clear,SquareCarryLoan719.patchKG,
    LowZero18KG.make,LowZero18KG.clear,Challenge.gateSlots_append,
    Baselines.rename_gateSlots,and_self]

theorem withLowK2_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (withLowK2 L ext control src dst body)+48=
      toffoliCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) ∧
    measurementCount (withLowK2 L ext control src dst body)+18=
      measurementCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have d := LowZero18LowK.kg_counts_diff L hw ext src dst h128 h129 hd he
  simp only [withLowK2,SquareCarryLoan719BF.withLowK2,toffoliCount_append,measurementCount_append,
    (patchKG_counts L _).1,(patchKG_counts L _).2.1,(patchKG_counts L _).2.2.1,(patchKG_counts L _).2.2.2,
    (SquareCarryLoan719BF.patchKG_counts L _).1,(SquareCarryLoan719BF.patchKG_counts L _).2.1,
    (SquareCarryLoan719BF.patchKG_counts L _).2.2.1,(SquareCarryLoan719BF.patchKG_counts L _).2.2.2,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem withLowK2_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (withLowK2 L ext control src dst body)⊆
      wires (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have m := LowZero18LowK.loan_make_support_subset L hw ext src dst h128 h129 hd he
  have c := LowZero18LowK.loan_clear_support_subset L hw ext src dst h128 h129 hd he
  simp only [withLowK2,SquareCarryLoan719BF.withLowK2,make,clear,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact m | exact c | exact Finset.Subset.refl _

theorem withLowK2_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    Challenge.gateSlots (withLowK2 L ext control src dst body)≤
      Challenge.gateSlots (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have m := LowZero18LowK.loan_make_slots_le L hw ext src dst h128 h129 hd he
  have c := LowZero18LowK.loan_clear_slots_le L hw ext src dst h128 h129 hd he
  simp only [withLowK2,SquareCarryLoan719BF.withLowK2,make,clear,patchKG,Challenge.gateSlots_append,
    Baselines.rename_gateSlots]
  omega

theorem raw_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    toffoliCount (raw L ext control)+144=toffoliCount (SquareCarryLoan719BF.raw L ext control) ∧
    measurementCount (raw L ext control)+54=measurementCount (SquareCarryLoan719BF.raw L ext control) := by
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c := withLowK2_counts_diff L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  have b := withLowK2_counts_diff L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a := withLowK2_counts_diff L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  simp only [raw,SquareCarryLoan719BF.raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,reflection,SquareCarryLoan719BF.reflection,
    toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem raw_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    wires (raw L ext control)⊆wires (SquareCarryLoan719BF.raw L ext control) := by
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c := withLowK2_support_subset L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  have b := withLowK2_support_subset L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a := withLowK2_support_subset L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  simp only [raw,SquareCarryLoan719BF.raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,reflection,SquareCarryLoan719BF.reflection,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact c | exact b | exact a | exact Finset.Subset.refl _

theorem raw_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (raw L ext control)≤Challenge.gateSlots (SquareCarryLoan719BF.raw L ext control) := by
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c := withLowK2_slots_le L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  have b := withLowK2_slots_le L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a := withLowK2_slots_le L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  simp only [raw,SquareCarryLoan719BF.raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,reflection,SquareCarryLoan719BF.reflection,Challenge.gateSlots_append,
    Baselines.rename_gateSlots]
  omega

private theorem tRename (f : Wire→Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem mRename (f : Wire→Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

theorem counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+144=toffoliCount (SquareCarryLoan719BF.program L) ∧
    measurementCount (program L)+54=measurementCount (SquareCarryLoan719BF.program L) := by
  have h := raw_counts_diff L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,SquareCarryLoan719BF.program,place,SquareCarryLoan719BF.place,
    fastCandidate,SquareCarryLoan719BF.fastCandidate,tRename,mRename] using h

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=52239 ∧ measurementCount (program L)=53021 := by
  have a := counts_diff L hw
  have b := SquareCarryLoan719BF.counts L hw
  constructor <;> omega

theorem slots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (SquareCarryLoan719BF.program L) := by
  have h := raw_slots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,SquareCarryLoan719BF.program,place,SquareCarryLoan719BF.place,
    fastCandidate,SquareCarryLoan719BF.fastCandidate,Baselines.rename_gateSlots] using h

theorem slots (L : ControlledPointLayout) (hw : L.Widths) : Challenge.gateSlots (program L)≤8000000 :=
  (slots_le L hw).trans (SquareCarryLoan719BF.slots L hw)

private theorem place_support_mono (L : ControlledPointLayout) (P Q : Program) (sub : wires P⊆wires Q) :
    wires (place L P)⊆wires (SquareCarryLoan719BF.place L Q) := by
  unfold place SquareCarryLoan719BF.place
  repeat' apply OneFlagReplay.rename_subset
  exact sub

theorem support_subset (L : ControlledPointLayout) (hw : L.Widths) :
    wires (program L)⊆wires (SquareCarryLoan719BF.program L) := by
  apply place_support_mono
  exact raw_support_subset L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L hw).trans (SquareCarryLoan719BF.support L hw hn)

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire k∉wires (program L) :=
  fun used=>SquareCarryLoan719BF.square_free L hw hn k hk (support_subset L hw used)

theorem retired_free719 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 719∉wires (program L) := square_free L hw hn 719 (by simp)
theorem retired_free768 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 768∉wires (program L) := square_free L hw hn 768 (by simp)
theorem retired_free718 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 718∉wires (program L) := square_free L hw hn 718 (by simp)

private theorem patchKG_physical (L : CuccaroStreamedSquareWideLayout) (R : KG)
    (hm : GatePhysical (LowZero18KG.make R))
    (hc : GatePhysical (LowZero18KG.clear R)) :
    GatePhysical (LowZero18Square.make L R) ∧ GatePhysical (LowZero18Square.clear L R) := by
  simp only [LowZero18KG.make,gatePhysical_append] at hm
  simp only [LowZero18KG.clear,gatePhysical_append] at hc
  have first : GatePhysical (renameProgram (earlyPerm L) R.Q1) :=
    gatePhysical_rename (earlyPerm L) (earlyPerm L).injective _ (by tauto)
  have last : GatePhysical (renameProgram (earlyPerm L) R.Q1c) :=
    gatePhysical_rename (earlyPerm L) (earlyPerm L).injective _ (by tauto)
  simp only [LowZero18Square.make,LowZero18Square.clear,SquareCarryLoan719.patchKG,
    LowZero18KG.make,LowZero18KG.clear,gatePhysical_append]
  tauto

private theorem withLowK2_physical_of_old (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (src dst : List Wire) (body : Program)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hlen : dst.length=2*src.length)
    (old : GatePhysical (FrontierSumCleanup1591LowK.withLowK2 L ext control src dst body)) :
    GatePhysical (withLowK2 L ext control src dst body) := by
  simp only [FrontierSumCleanup1591LowK.withLowK2,gatePhysical_append] at old
  have nd := LowZero18LowK.kg_nodup L control hn ext src dst hs hd he.nodup he.away
  have ph := LowZero18LowK.kg_physical L hw ext src dst h128 h129 hlen he.len nd
  have kernels := patchKG_physical L (LowZero18LowK.kg L ext src dst) ph.1 ph.2
  have bodyNew : GatePhysical (renameProgram (foldPerm L ext) body) :=
    gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ (by tauto)
  simp only [withLowK2,gatePhysical_append]
  tauto

private theorem raw_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) : GatePhysical (raw L ext control) := by
  have old := ControlLoan1589BFFold.physical L hw ext control hn he
  simp only [ControlLoan1589BFFold.program,FrontierSumCleanup1591Raw.accBranchCK,
    FrontierSumCleanup1591Raw.accMiddleCK,ControlLoan1589BFFold.branchBF,
    ControlLoan1589BFFold.branchAF,gatePhysical_append] at old
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have sc := source_counts L
  have c := withLowK2_physical_of_old L hw ext control hn he L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) sc.2.2.1 (fun _=>le_rfl)
    (by omega) (by omega) (by rw [hw.core.product,sum]) old.1.1.1.1.2
  have b := withLowK2_physical_of_old L hw ext control hn he L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) sc.2.1 sc.2.2.2
    (by omega) (by omega) (by omega) old.1.1.2
  have a := withLowK2_physical_of_old L hw ext control hn he L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) sc.1 sc.2.2.2
    (by omega) (by omega) (by omega) old.1.2
  have r := gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ old.2
  simp only [raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,reflection,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨old.1.1.1.1.1,c⟩,old.1.1.1.2⟩,b⟩,a⟩,r⟩

private theorem control_nd (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
  have nd := L.streamedSquare_control_nodup hw hn
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp nd q
  simp only [List.count_cons] at h ⊢
  omega

private theorem place_physical (L : ControlledPointLayout) (P : Program) (hp : GatePhysical P) :
    GatePhysical (place L P) := by
  unfold place
  apply gatePhysical_rename (ControlLoan1589Square.swap L) (ControlLoan1589Square.swap L).injective
  apply gatePhysical_rename (Prefix1590Square.swap L) (Prefix1590Square.swap L).injective
  apply gatePhysical_rename (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.swap L).injective
  apply gatePhysical_rename (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.swap L).injective
  apply gatePhysical_rename (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.swap L).injective
  apply gatePhysical_rename (OwnQ5Square.swap L) (OwnQ5Square.swap L).injective
  apply gatePhysical_rename (OwnQ4Square.swap L) (OwnQ4Square.swap L).injective
  apply gatePhysical_rename (OwnGuardSquare.swap L) (OwnGuardSquare.swap L).injective
  apply gatePhysical_rename (OwnPlusSquare.swap L) (OwnPlusSquare.swap L).injective
  exact gatePhysical_rename (Square5Placement.blockPerm L 202) (Square5Placement.blockPerm L 202).injective _ hp

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (program L) :=
  place_physical L _ (raw_physical L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (control_nd L hw hn) (ECDSAAdd.Entrant.kext_ok L hw hn))

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588LowZeroFinal =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588BFFinal
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareResources

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588LowZeroFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite FrontierEntry1591Callers
  ControlLoan1589BFFinal
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  Offset.gen L (division Rolling1588.entryKernel L) (LowZero18Square.program L)
    (exit Rolling1588.exitKernel L) cx cy

private def Metrics (P Q : Program) : Prop :=
  toffoliCount P+144=toffoliCount Q ∧ measurementCount P+54=measurementCount Q ∧
    gateSlots P≤gateSlots Q

private theorem gen_metrics_of_shapes (L : ControlledPointLayout) (D : Fp→Program)
    (S Old P G G0 : Program) (cx cy : Fp)
    (hG : G=Offset.gen L D S P cx cy) (hG0 : G0=Offset.gen L D Old P cx cy)
    (hs : Metrics S Old) : Metrics G G0 := by
  subst G G0
  simp only [Metrics,Offset.gen,Offset.mid,Offset.generic,toffoliCount_append,
    measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots] at hs ⊢
  exact ⟨by omega,by omega,by omega⟩

private theorem gen_metrics (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Metrics (gen L cx cy) (Rolling1588BFFinal.gen L cx cy) := by
  have counts:=LowZero18Square.counts_diff L hw
  exact gen_metrics_of_shapes L (division Rolling1588.entryKernel L)
    (LowZero18Square.program L) (SquareCarryLoan719BF.program L) (exit Rolling1588.exitKernel L)
    (gen L cx cy) (Rolling1588BFFinal.gen L cx cy) cx cy
    (by unfold gen; rfl) (by unfold Rolling1588BFFinal.gen; rfl)
    ⟨counts.1,counts.2,LowZero18Square.slots_le L hw⟩

theorem gen_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+144=toffoliCount (Rolling1588BFFinal.gen L cx cy) ∧
    measurementCount (gen L cx cy)+54=measurementCount (Rolling1588BFFinal.gen L cx cy) :=
  ⟨(gen_metrics L hw cx cy).1,(gen_metrics L hw cx cy).2.1⟩

private theorem wrapper_metrics (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Metrics P Q) :
    Metrics (Edges.wrapper L C cy P) (Edges.wrapper L C cy Q) := by
  simp only [Metrics,Edges.wrapper,Edges.finiteProgram,toffoliCount_append,
    measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots] at h ⊢
  exact ⟨by omega,by omega,by omega⟩

private theorem gen_subset_of_shapes (L : ControlledPointLayout) (D : Fp→Program)
    (S Old P G G0 : Program) (cx cy : Fp)
    (hG : G=Offset.gen L D S P cx cy) (hG0 : G0=Offset.gen L D Old P cx cy)
    (hs : wires S⊆wires Old) : wires G⊆wires G0 := by
  subst G G0
  simp only [Offset.gen,Offset.mid,Offset.generic,wires_append,renameProgram_support]
  repeat' first | apply Finset.union_subset_union | apply Finset.image_subset_image
  all_goals first | exact hs | exact Finset.Subset.refl _

theorem gen_support_subset (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (gen L cx cy)⊆wires (Rolling1588BFFinal.gen L cx cy) :=
  gen_subset_of_shapes L (division Rolling1588.entryKernel L)
    (LowZero18Square.program L) (SquareCarryLoan719BF.program L) (exit Rolling1588.exitKernel L)
    (gen L cx cy) (Rolling1588BFFinal.gen L cx cy) cx cy
    (by unfold gen; rfl) (by unfold Rolling1588BFFinal.gen; rfl)
    (LowZero18Square.support_subset L hw)

private theorem wrapper_subset (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : wires P⊆wires Q) :
    wires (Edges.wrapper L C cy P)⊆wires (Edges.wrapper L C cy Q) := by
  simp only [Edges.wrapper,Edges.finiteProgram,wires_append,renameProgram_support]
  repeat' first | apply Finset.union_subset_union | apply Finset.image_subset_image
  all_goals first | exact h | exact Finset.Subset.refl _

private theorem qubits_mono (P Q : Program) (h : wires P⊆wires Q) : qubits P≤qubits Q := by
  change (ioWires∪wires P).card≤(ioWires∪wires Q).card
  exact Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl _) h)

theorem gen_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  exact Offset.genFFused_ok L hw hn _ _ _
    (FrontierEntry1591Callers.exit_correct Rolling1588.exitKernel
      Rolling1588.exitKernel_support Rolling1588.exit_correct L hw hn)
    (FrontierEntry1591Callers.division_step Rolling1588.entryKernel
      Rolling1588.entryKernel_support Rolling1588.entry_correct
      L hw hn config.1 above config.2.1 config.2.2)
    (LowZero18Square.step L hw hn) hc

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  (gen_support_subset L hw cx cy).trans (Rolling1588BFFinal.gen_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) :=
  Offset.gen_physical L hw hn _ _ _
    (division_physical Rolling1588.entryKernel Rolling1588.entryKernel_support
      Rolling1588.entryKernel_physical L hw hn)
    (LowZero18Square.physical L hw hn)
    (placed_physical Rolling1588.exitKernel Rolling1588.exitKernel_support
      Rolling1588.exitKernel_physical L hw hn) cx cy

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1588 :=
  (qubits_mono _ _ (wrapper_subset layout C cy _ _
    (gen_support_subset layout layout_widths cx cy))).trans
    (Rolling1588BFFinal.wrapper_qubits C cx cy)

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2153226 := by
  have diff:=(wrapper_metrics layout (.some hc) cy _ _ (gen_metrics layout layout_widths cx cy)).1
  have old:=Rolling1588BFFinal.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1499931 := by
  have diff:=(wrapper_metrics layout (.some hc) cy _ _ (gen_metrics layout layout_widths cx cy)).2.1
  have old:=Rolling1588BFFinal.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50116097 :=
  (wrapper_metrics layout C cy _ _ (gen_metrics layout layout_widths cx cy)).2.2.trans
    (Rolling1588BFFinal.wrapper_slots C cx cy)

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2153226,1499931,1588,50116097⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (gen_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2153226 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C)≤1499931 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C)≤1588 := by
  cases C with
  | zero => change qubits []≤1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50116097 := by
  cases C with
  | zero => simp [program,gateSlots]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1499931
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50116097
    rw [normalize_slots];exact program_gateSlots C

end ECDSAAdd.Entrant.Rolling1588LowZeroFinal
end -- original module boundary

-- Selected checked E1 branch follows; the audited LowZero18 branch is omitted.

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Square =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.SquareCarryLoan719BFProof

/-! Remove only the BF square's final reflection. All719 loans stay intact. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
  SquareCarryLoan719BF
attribute [local irreducible] run wires

def core (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  branchCK L ext control++branchBF L ext control++branchAF L ext control

def fastCore (L : ControlledPointLayout) : Program :=
  core L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def program (L : ControlledPointLayout) : Program := place L (fastCore L)

def reflectedTail (L : ControlledPointLayout) : Program :=
  place L (reflection L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L))

theorem raw_split (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) :
    raw L ext control=core L ext control++reflection L ext := rfl

theorem place_append (L : ControlledPointLayout) (P Q : Program) :
    place L (P++Q)=place L P++place L Q := by
  simp only [place,renameProgram,List.map_append]

theorem program_split (L : ControlledPointLayout) :
    SquareCarryLoan719BF.program L=program L++reflectedTail L := by
  simp only [SquareCarryLoan719BF.program,SquareCarryLoan719BF.fastCandidate,
    raw_split,place_append,program,fastCore,reflectedTail]

theorem raw_core_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (core L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (core L ext control) records s).basis=
      SquareReduction.p-1-
        (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
          (if s.basis control then K else 0))%SquareReduction.p) ∧
    ∀q,q∉L.core.out → (run (core L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := ControlLoan1589BFFold.resAF PA OB enabled
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have low (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.low t=A := regValue_congr _ _ _ (fun q hq => hf.2 q (lowAway q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.high t=B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.sum t=B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.product t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue ext t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (SquareCarryLoan719BF.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := SquareCarryLoan719BF.branchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OB hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := (stepC.seq stepB).seq stepA
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := ControlLoan1589BFFold.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  have oaLt : OA<SquareReduction.p := ofCast_lt _ _
  have reflected : OA=SquareReduction.p-1-
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) := by
    change SquareReduction.p-1-OA=
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) at exactResult
    omega
  exact ⟨phase,value.trans reflected,frame⟩


open Secp256k1 MappedCompressed CompressedPointDialog

theorem fastCore_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(((X+p-(if B then Y*Y else 0)%p)%p+(if B then ControlLoan1589BFFold.K else 0))%p) ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := raw_core_correct K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean (kext_ok L hw hn) hz
  simpa only [fastCore,hb,hp,pow_two] using kernel


theorem fastCore_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  have fresh:=fastCore_correct L hw hn X.val Y.val G X.isLt s m v.generic v.x v.y v.clean
  have prior:=ControlLoan1589BFSquare.fastCandidate_correct L hw hn X.val Y.val G X.isLt s []
    v.generic v.x v.y v.clean
  have canonical:=SquareCarryLoan719BF.candidate_correct L hw hn X Y G origin s [] v
  have eq:=SquareCarryLoan719BF.fastCandidate_state_eq L hw hn X.val Y.val X.isLt s [] []
    v.x v.y v.clean
  rw [eq] at canonical
  have value:=prior.2.1.symm.trans canonical.2.x
  rw [value] at fresh
  exact fresh

private theorem place_relabel (L : ControlledPointLayout) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool) (hf : ∀q,q∉L.dialogPool → e q=q)
    (P : Program) (s : State) (m : List Bool)
    (before : regValue L.dialogPool s.basis=0) (after : regValue L.dialogPool (run P m s).basis=0) :
    run (renameProgram e P) m s=run P m s :=
  Square5Placement.pool_relabel_state_eq L e hp hf P s m before after

/-- Transport the complete State before taking any projection. -/
theorem place_run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (P : Program) (s : State) (m : List Bool)
    (before : regValue L.dialogPool s.basis=0) (after : regValue L.dialogPool (run P m s).basis=0) :
    run (place L P) m s=run P m s := by
  have a0:=place_relabel L (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) P s m before after
  have a1:=place_relabel L (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw) (OwnPlusSquare.outside L hw)
    _ s m before (by rw [a0];exact after)
  have a2:=place_relabel L (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw) (OwnGuardSquare.outside L hw)
    _ s m before (by rw [a1,a0];exact after)
  have a3:=place_relabel L (OwnQ4Square.swap L) (OwnQ4Square.pool L hw) (OwnQ4Square.outside L hw)
    _ s m before (by rw [a2,a1,a0];exact after)
  have a4:=place_relabel L (OwnQ5Square.swap L) (OwnQ5Square.pool L hw) (OwnQ5Square.outside L hw)
    _ s m before (by rw [a3,a2,a1,a0];exact after)
  have a5:=place_relabel L (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.pool L hw)
    (OwnDiagAll12PlacedQ6.outside L hw) _ s m before (by rw [a4,a3,a2,a1,a0];exact after)
  have a6:=place_relabel L (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.pool L hw)
    (OwnDiagAll12PlacedQ7.outside L hw) _ s m before (by rw [a5,a4,a3,a2,a1,a0];exact after)
  have a7:=place_relabel L (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.pool L hw)
    (PrefixFrontierSquare1591.outside L hw) _ s m before (by rw [a6,a5,a4,a3,a2,a1,a0];exact after)
  have a8:=place_relabel L (Prefix1590Square.swap L) (Prefix1590Square.pool L hw)
    (Prefix1590Square.outside L hw) _ s m before (by rw [a7,a6,a5,a4,a3,a2,a1,a0];exact after)
  have a9:=place_relabel L (ControlLoan1589Square.swap L) (ControlLoan1589Square.pool L hw)
    (ControlLoan1589Square.outside L hw) _ s m before (by rw [a8,a7,a6,a5,a4,a3,a2,a1,a0];exact after)
  simpa only [place,a8,a7,a6,a5,a4,a3,a2,a1,a0] using a9


private theorem pool_away_x (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have dis:=(List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  intro hx
  have resident : q∈CompressedPointSquare.residents L := by
    simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis resident hq

theorem boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (program L) m s).phase=s.phase ∧
    regValue L.point.x (run (program L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (program L) m s).basis q=s.basis q := by
  have result:=fastCore_boundary L hw hn X Y G origin s m v
  obtain ⟨out,heq⟩ : ∃out : State,run (fastCore L) m s=out := ⟨_,rfl⟩
  rw [heq] at result
  have clean : regValue L.dialogPool out.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x L hn q hq)),v.clean]
  have eq:=place_run_eq L hw (fastCore L) s m v.clean (by rw [heq];exact clean)
  change run (program L) m s=run (fastCore L) m s at eq
  rw [eq,heq]
  exact result

theorem support_subset (L : ControlledPointLayout) :
    wires (program L)⊆wires (SquareCarryLoan719BF.program L) := by
  rw [program_split,wires_append]
  exact Finset.subset_union_left

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L).trans (SquareCarryLoan719BF.support L hw hn)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  have old:=SquareCarryLoan719BF.physical L hw hn
  rw [program_split,gatePhysical_append] at old
  exact old.1

theorem free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program L) := by
  by_cases h : i=719
  · subst i;exact fun used=>SquareCarryLoan719BF.retired_free719 L hw hn (support_subset L used)
  · exact fun used=>SquareCarryLoan719BF.square_free L hw hn i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;tauto) (support_subset L used)

theorem place_counts (L : ControlledPointLayout) (P : Program) :
    toffoliCount (place L P)=toffoliCount P ∧ measurementCount (place L P)=measurementCount P := by
  simp only [place,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,and_self]

theorem reflectedTail_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (reflectedTail L)=255 ∧ measurementCount (reflectedTail L)=255 := by
  have r:=(L.dialogStreamedSquareWide.measured_small_operation_counts
    (L.dialogStreamedSquareWide_widths hw)).2.2
  simpa only [reflectedTail,(place_counts _ _).1,(place_counts _ _).2,reflection,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using r

theorem counts_delta (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+255=toffoliCount (SquareCarryLoan719BF.program L) ∧
    measurementCount (program L)+255=measurementCount (SquareCarryLoan719BF.program L) := by
  rw [program_split,toffoliCount_append,measurementCount_append,
    (reflectedTail_counts L hw).1,(reflectedTail_counts L hw).2]
  exact ⟨rfl,rfl⟩

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=52128 ∧ measurementCount (program L)=52820 := by
  have d:=counts_delta L hw
  have c:=SquareCarryLoan719BF.counts L hw
  constructor <;> omega

theorem slots_le (L : ControlledPointLayout) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (SquareCarryLoan719BF.program L) := by
  rw [program_split,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.ReflectionE1Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.E1Merge =====
section
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectForwardProof
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectValues
-- consolidated import: import ECDSAAdd.Arithmetic.Compare
-- consolidated import: import ECDSAAdd.Arithmetic.ComparePhysical
-- consolidated import: import ECDSAAdd.Arithmetic.MaskedConstant
-- consolidated import: import ECDSAAdd.Arithmetic.MappedSources
-- consolidated import: import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.Copy
-- consolidated import: import ECDSAAdd.Arithmetic.Rotate
-- consolidated import: import ECDSAAdd.Arithmetic.Reduction
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredGateSupport
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectSupport
-- consolidated import: import ECDSAAdd.Baselines.SlotAlgebra
-- consolidated import: import ECDSAAdd.Baselines.SlotMapped
-- consolidated import: import ECDSAAdd.Baselines.SlotNativeFirst

set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1Merge
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum

/-! ### Arithmetic of the merged first tick -/

theorem p_val : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  norm_num [ECDSAAdd.p]

/-- bit 0 of the selected constant `g·k − f·p`. -/
def ksel0 (k : Nat) (G f : Bool) : Bool := (G && decide (k%2=1)) ^^ f
/-- low bit of the input implied by `(g,f,par)`. -/
def x0 (k : Nat) (G f par : Bool) : Bool := par ^^ ksel0 k G f

/-- Constant added to `x>>1` to obtain the first-tick `K` word directly. -/
def tk (k : Nat) (G f par : Bool) : Nat :=
  if f then (if G then (kConstant false par+2^258-(p+par.toNat-(x0 k G f par).toNat-k)/2)%2^258 else 0)
  else if G then (kConstant false par+((x0 k G f par).toNat+k-par.toNat)/2)%2^258
  else kConstant false par

def delta (par : Bool) : Nat := if par then p else 2^257-p

def thr (k : Nat) (G par : Bool) : Nat := if G then (if par then (k+p+1)/2 else (k+1)/2) else 0

theorem hC_val : hConstant = 57896044618658097711785492504343953926634992332820282019728792003954417335832 := by
  norm_num [hConstant, ECDSAAdd.p]
theorem kC_val (par : Bool) : kConstant false par =
    if par then 405272312330606683982498447530407677486444946329741974138101544027698101223913
    else 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  cases par <;> norm_num [kConstant, ECDSAAdd.p]


theorem arith (k X : Nat) (hk : k<p) (hX : X<p) (G : Bool) :
    let f := decide (2^256-1-(if G then 2^256-p+k else 0)<X)
    let dx := (X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    decide (X%2=1)=x0 k G f par ∧
    (X/2+tk k G f par)%2^258=K ∧
    H=dx/2+(if par then hConstant else 0) ∧
    f=decide (H<thr k G par) ∧
    tk k G f par<2^258 := by
  intro f dx par K H
  rw [p_val] at hk hX
  simp only [f,dx,par,K,H,tk,delta,thr,x0,ksel0,kC_val,hC_val,p_val,Nat.reducePow]
  clear H K par dx f
  cases G
  · have e1 : (X+0)%115792089237316195423570985008687907853269984665640564039457584007908834671663=X := Nat.mod_eq_of_lt (by omega)
    have e2 : decide (115792089237316195423570985008687907853269984665640564039457584007913129639936-1-0<X)=false := by
      simp only [decide_eq_false_iff_not]; omega
    simp only [if_false,Bool.false_eq_true,e1,e2,Bool.false_and,Bool.false_xor,Bool.xor_false]
    rcases Nat.mod_two_eq_zero_or_one X with h|h <;>
    simp only [h,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
      Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true] <;>
    exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega),by (first | exact True.intro | omega),by (first | exact True.intro | (rw [eq_comm, decide_eq_true_iff]; omega) | (rw [eq_comm, decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
  · simp only [if_true,Bool.true_and]
    by_cases hf : 115792089237316195423570985008687907853269984665640564039457584007908834671663≤X+k
    · have e1 : (X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=X+k-115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
        rw [Nat.mod_eq_sub_mod hf,Nat.mod_eq_of_lt (by omega)]
      have e2 : decide (115792089237316195423570985008687907853269984665640564039457584007913129639936-1-(115792089237316195423570985008687907853269984665640564039457584007913129639936-115792089237316195423570985008687907853269984665640564039457584007908834671663+k)<X)=true := by
        simp only [decide_eq_true_iff]; omega
      simp only [e1,e2,Bool.xor_true]
      clear e1 e2
      rcases Nat.mod_two_eq_zero_or_one (X+k-115792089237316195423570985008687907853269984665640564039457584007908834671663) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega),by (first | exact True.intro | omega),by (first | exact True.intro | (rw [eq_comm, decide_eq_true_iff]; omega) | (rw [eq_comm, decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
    · have e1 : (X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=X+k := Nat.mod_eq_of_lt (by omega)
      have e2 : decide (115792089237316195423570985008687907853269984665640564039457584007913129639936-1-(115792089237316195423570985008687907853269984665640564039457584007913129639936-115792089237316195423570985008687907853269984665640564039457584007908834671663+k)<X)=false := by
        simp only [decide_eq_false_iff_not]; omega
      simp only [e1,e2,Bool.xor_false]
      clear e1 e2
      rcases Nat.mod_two_eq_zero_or_one (X+k) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega),by (first | exact True.intro | omega),by (first | exact True.intro | (rw [eq_comm, decide_eq_true_iff]; omega) | (rw [eq_comm, decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩

/-! ### Circuit -/

def cmpC : Nat := 2^256-p

def srcR (w : Nat → Wire) : List Wire := wireBlock w 0 256
def xR (w : Nat → Wire) : List Wire := wireBlock w 770 256
def cR (w : Nat → Wire) : List Wire := wireBlock w 256 256
def hR (w : Nat → Wire) : List Wire := wireBlock w 0 258
def kR (w : Nat → Wire) : List Wire := wireBlock w 770 258
def tR (w : Nat → Wire) : List Wire := wireBlock w 1029 256
def hpR (w : Nat → Wire) : List Wire := wireBlock w 1 257
def aC (w : Nat → Wire) : List Wire := wireBlock w 1540 257
def hC2 (w : Nat → Wire) : List Wire := wireBlock w 1540 256
def hp8 (w : Nat → Wire) : List Wire := wireBlock w 1 256
def hC3 (w : Nat → Wire) : List Wire := wireBlock w 1540 255

def comparePart (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (srcR w) (cmpC+k)++notRegister (srcR w)++
  compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514)++
  notRegister (srcR w)++maskedConstant g (srcR w) (cmpC+k)

def parGates (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  [.CX (w 770) (w 1028)]++(if k%2=1 then [.CX g (w 1028)] else [])++[.CX (w 514) (w 1028)]++
  [.CX (w 1028) (w 770)]++(if k%2=1 then [.CX g (w 770)] else [])++[.CX (w 514) (w 770)]

def prodPart (w : Nat → Wire) (g : Wire) : Program :=
  [.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)]

def c1 (k : Nat) : Nat := tk k false false false
def cg (k : Nat) : Nat := tk k true false false ^^^ tk k false false false
def cf (k : Nat) : Nat := tk k true true false ^^^ tk k true false false
def cp (k : Nat) : Nat := tk k false false true ^^^ tk k false false false
def cgp (k : Nat) : Nat :=
  tk k true false true ^^^ tk k true false false ^^^ tk k false false true ^^^ tk k false false false
def cfp (k : Nat) : Nat :=
  tk k true true true ^^^ tk k true true false ^^^ tk k true false true ^^^ tk k true false false

def loadK (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  xorConstant (hR w) (c1 k)++maskedConstant g (hR w) (cg k)++maskedConstant (w 514) (hR w) (cf k)++
  maskedConstant (w 1028) (hR w) (cp k)++maskedConstant (w 721) (hR w) (cgp k)++
  maskedConstant (w 722) (hR w) (cfp k)

def kAddM (w : Nat → Wire) : Program := mappedAdd (mappedRead (hR w) false) (kR w) (aC w) (w 1797)

def dBits (w : Nat → Wire) : List MappedBit := (List.range 257).map (fun j =>
  let a := (2^257-p).testBit j
  let b := p.testBit j
  if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some (w 1028),flip:=a})

def hAddM (w : Nat → Wire) : Program := mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)

/-- `hAddM` with its first carry trimmed. The first mapped bit is the literal `1`
(`2^257-p` and `p` are both odd) and the carry-in `w 1797` is clean, so the first
majority's Toffoli `CCX (w 1) (w 1797) (w 1540)` never fires; it is dropped. -/
def hPost (w : Nat → Wire) : Program :=
  mappedAdd (dBits w).tail (hpR w).tail (hC2 w).tail (w 1540) ++
    mappedEraseCarry {wire:=none,flip:=true} (w 1) (w 1797) (w 1540) ++
    mappedSum {wire:=none,flip:=true} (w 1) (w 1797)

def hAddT (w : Nat → Wire) : Program := [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ hPost w


def thrA (k : Nat) : Nat := (k+1)/2
def thrB (k : Nat) : Nat := (k+1)/2 ^^^ (k+p+1)/2

def loadT (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (tR w) (thrA k)++maskedConstant (w 721) (tR w) (thrB k)

/-- Compare-first constant addition `x ↦ x + g·k mod p` merged into the direct first tick. -/
def merged (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  comparePart w g k++(parGates w g k++rotateRight (kR w))++prodPart w g++loadK w g k++kAddM w++loadK w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddT w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]

/-! ### Layout facts -/

section Layout
variable (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
include hn

theorem mem_blk (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) :
    w i ∈ wireBlock w a n ↔ a ≤ i ∧ i < a + n := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := skywalkPool_index_inj w hn i j hi (by omega) he.symm
    omega
  · intro h
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem w_ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j :=
  index_ne w hn i j hi hj h

omit hn in
theorem blk_sub (a n b m : Nat) (h1 : b≤a) (h2 : a+n≤b+m) : ∀q∈wireBlock w a n,q∈wireBlock w b m := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem blk_nd (a n : Nat) (ha : a+n≤1798) : (wireBlock w a n).Nodup := block_nodup w hn a n ha

theorem blk_dis (a n b m : Nat) (ha : a+n≤1798) (hb : b+m≤1798) (sep : a+n≤b ∨ b+m≤a) :
    List.Disjoint (wireBlock w a n) (wireBlock w b m) := block_disjoint w hn a n b m ha hb sep

theorem g_out (g : Wire) (hg : g∉skywalkPoolWires w) (a n : Nat) (ha : a+n≤1798) : g∉wireBlock w a n :=
  fun h => hg (blk_sub w a n 0 1798 (by omega) (by omega) g h)

theorem g_ne (g : Wire) (hg : g∉skywalkPoolWires w) (i : Nat) (hi : i<1798) : g≠w i := by
  intro e; apply hg; rw [e]
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

end Layout


/-! ### Frame -/

def mutL (w : Nat → Wire) : List Wire := hR w++kR w++tR w++[w 1028,w 514,w 721,w 722]

def MF (w : Nat → Wire) (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState) : Prop :=
  regValue (hR w) s=H ∧ regValue (kR w) s=X ∧ regValue (tR w) s=T ∧
  s (w 1028)=par ∧ s (w 514)=f ∧ s (w 721)=gp ∧ s (w 722)=fp ∧ ∀q,q∉mutL w → s q=b0 q

theorem keep (R : List Wire) (s t : BasisState) (hf : ∀q,q∉R → t q=s q) (C : List Wire)
    (hC : ∀q∈C,q∉R) : regValue C t=regValue C s :=
  regValue_congr C t s (fun q hq => hf q (hC q hq))

section Steps
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem hR_nd : (hR w).Nodup := blk_nd w hn 0 258 (by omega)
theorem kR_nd : (kR w).Nodup := blk_nd w hn 770 258 (by omega)
theorem tR_nd : (tR w).Nodup := blk_nd w hn 1029 256 (by omega)

theorem hR_kR : ∀q∈kR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 770 258 (by omega) (by omega) (by omega)) h hq
theorem hR_tR : ∀q∈tR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem kR_hR : ∀q∈hR w,q∉kR w := fun q hq h => hR_kR w hn q h hq
theorem kR_tR : ∀q∈tR w,q∉kR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 770 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem tR_hR : ∀q∈hR w,q∉tR w := fun q hq h => hR_tR w hn q h hq
theorem tR_kR : ∀q∈kR w,q∉tR w := fun q hq h => kR_tR w hn q h hq

theorem nb (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) (sep : i < a ∨ a + n ≤ i) : w i ∉ wireBlock w a n :=
  block_not_mem w hn i a n hi ha sep

theorem out_of_mut (R : List Wire) (hR' : ∀q∈R,q∈mutL w) (q : Wire) (hq : q∉mutL w) : q∉R :=
  fun h => hq (hR' q h)

theorem hR_mut : ∀q∈hR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem kR_mut : ∀q∈kR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem tR_mut : ∀q∈tR w,q∈mutL w := fun q hq => by simp [mutL,hq]

/-- An operation that changes only the `H` block. -/
theorem stepH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉hR w → t.basis q=s.basis q) (H' : Nat)
    (hv : regValue (hR w) t.basis=H') : MF w b0 H' X T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨hv,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (hR_kR w hn)]; exact h2
  · rw [keep _ _ _ hf _ (hR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 0 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 0 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 0 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 0 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (hR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the `K` block. -/
theorem stepK (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉kR w → t.basis q=s.basis q) (X' : Nat)
    (hv : regValue (kR w) t.basis=X') : MF w b0 H X' T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,hv,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (kR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (kR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 770 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 770 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 770 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (kR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the threshold block. -/
theorem stepT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉tR w → t.basis q=s.basis q) (T' : Nat)
    (hv : regValue (tR w) t.basis=T') : MF w b0 H X T' par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,?_,hv,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (tR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (tR_kR w hn)]; exact h2
  · rw [hf _ (nb w hn 1028 1029 256 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 1029 256 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 1029 256 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 1029 256 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (tR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes one scalar wire `w j` of the frame. -/
theorem stepBit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State) (j : Nat)
    (hj : j=1028 ∨ j=514 ∨ j=721 ∨ j=722)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q≠w j → t.basis q=s.basis q) :
    MF w b0 H X T (if j=1028 then t.basis (w j) else par) (if j=514 then t.basis (w j) else f)
      (if j=721 then t.basis (w j) else gp) (if j=722 then t.basis (w j) else fp) t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have hjr : j<1798 := by omega
  have nh : w j∉hR w := nb w hn j 0 258 hjr (by omega) (by omega)
  have nk : w j∉kR w := nb w hn j 770 258 hjr (by omega) (by omega)
  have nt : w j∉tR w := nb w hn j 1029 256 hjr (by omega) (by omega)
  have ne (i : Nat) (hi : i<1798) (hij : i≠j) : w i≠w j := w_ne w hn i j hi hjr hij
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nh (e ▸ hq)))]; exact h1
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nk (e ▸ hq)))]; exact h2
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nt (e ▸ hq)))]; exact h3
  · by_cases e : j=1028
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 1028 (by omega) (Ne.symm e))]; exact h4
  · by_cases e : j=514
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 514 (by omega) (Ne.symm e))]; exact h5
  · by_cases e : j=721
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 721 (by omega) (Ne.symm e))]; exact h6
  · by_cases e : j=722
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 722 (by omega) (Ne.symm e))]; exact h7
  · intro q hq
    have : q≠w j := by
      intro e; apply hq; rw [e]
      rcases hj with rfl|rfl|rfl|rfl <;> simp [mutL]
    rw [hf q this]; exact h8 q hq

end Steps


/-! ### Concrete steps -/

theorem run_cx (a b : Wire) (m : List Bool) (s : State) :
    run [.CX a b] m s=⟨s.phase,writeBit s.basis b (s.basis b ^^ s.basis a)⟩ := rfl
theorem run_ccx (a b c : Wire) (m : List Bool) (s : State) :
    run [.CCX a b c] m s=⟨s.phase,writeBit s.basis c (s.basis c ^^ (s.basis a && s.basis b))⟩ := rfl
theorem run_x (a : Wire) (m : List Bool) (s : State) :
    run [.X a] m s=⟨s.phase,writeBit s.basis a (!s.basis a)⟩ := rfl

theorem run_meas_and (t a b : Wire) (m : List Bool) (s : State) (ha : a≠t) (hb : b≠t)
    (ht : s.basis t=(s.basis a && s.basis b)) :
    run [.measureX t [] [.CZ a b]] m s=⟨s.phase,writeBit s.basis t false⟩ := by
  simp only [run,measureAndCorrect]
  cases m.headD false <;> simp [correct,writeBit,Function.update_of_ne ha,Function.update_of_ne hb,ht]

section Concrete
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem kR_split (s : BasisState) :
    regValue (kR w) s=(s (w 770)).toNat+2*regValue (wireBlock w 771 257) s := by
  have e : kR w=w 770::wireBlock w 771 257 := by
    simp [kR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 770) <;> simp [regValue,h]

theorem hR_split (s : BasisState) :
    regValue (hR w) s=(s (w 0)).toNat+2*regValue (hpR w) s := by
  have e : hR w=w 0::hpR w := by
    simp [hR,hpR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 0) <;> simp [regValue,h]

theorem hR_src (s : BasisState) :
    regValue (hR w) s=regValue (srcR w) s+2^256*regValue (wireBlock w 256 2) s := by
  have e : hR w=srcR w++wireBlock w 256 2 := by
    rw [hR,srcR,wireBlock_append]
  rw [e,regValue_append,srcR,wireBlock_length]

theorem kR_x (s : BasisState) :
    regValue (kR w) s=regValue (xR w) s+2^256*regValue (wireBlock w 1026 2) s := by
  have e : kR w=xR w++wireBlock w 1026 2 := by
    rw [kR,xR,wireBlock_append]
  rw [e,regValue_append,xR,wireBlock_length]

theorem kR_low (s : BasisState) :
    regValue (kR w) s=regValue (wireBlock w 770 257) s+2^257*regValue (wireBlock w 1027 1) s := by
  have e : kR w=wireBlock w 770 257++wireBlock w 1027 1 := by
    rw [kR,wireBlock_append]
  rw [e,regValue_append,wireBlock_length]

/-- A CX targeting the parity wire. -/
theorem stepParCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 1028) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) :
    Triple (MF w b0 H X T par f gp fp) [.CX c (w 1028)] (MF w b0 H X T (par ^^ cv) f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 1028)
    (s.basis (w 1028) ^^ s.basis c)⟩ 1028 (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit,h.2.2.2.1,hcv s.basis h] using this

/-- A CX targeting bit 0 of the K block. -/
theorem stepLowCX (b0 : BasisState) (H Y T : Nat) (b par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 770) (hcv : ∀s : BasisState,MF w b0 H (2*Y+b.toNat) T par f gp fp s → s c=cv) :
    Triple (MF w b0 H (2*Y+b.toNat) T par f gp fp) [.CX c (w 770)]
      (MF w b0 H (2*Y+(b ^^ cv).toNat) T par f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have m770 : w 770∈kR w := (mem_blk w hn 770 770 258 (by omega) (by omega)).mpr (by omega)
  have rest : ∀q∈wireBlock w 771 257,q≠w 770 := fun q hq e =>
    nb w hn 770 771 257 (by omega) (by omega) (by omega) (e ▸ hq)
  apply stepK w hn b0 H _ T par f gp fp s _ h
  · intro q hq; have : q≠w 770 := fun e => hq (e ▸ m770)
    simp [writeBit,Function.update_of_ne this]
  · have sp := kR_split w hn s.basis
    have sp2 := kR_split w hn (writeBit s.basis (w 770) (s.basis (w 770) ^^ s.basis c))
    rw [h.2.1] at sp
    rw [sp2,regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,Function.update_of_ne (rest q hq)])]
    rw [hcv s.basis h]
    simp only [writeBit,Function.update_self]
    cases hb : s.basis (w 770) <;> cases b <;> cases cv <;> simp [hb] at sp ⊢ <;> omega

end Concrete


section Concrete2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepXorH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (xorConstant (hR w) v) (MF w b0 (H^^^v) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := xorConstant_correct (hR w) (hR_nd w hn) v (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1])⟩

theorem stepMaskH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉hR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (hR w) v)
      (MF w b0 (H^^^(if cv then v else 0)) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (hR w) v (hR_nd w hn) hc
    (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1,hcv s.basis h])⟩

theorem stepMaskT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉tR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^256) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (tR w) v)
      (MF w b0 H X (T^^^(if cv then v else 0)) par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (tR w) v (tR_nd w hn) hc
    (by simpa [tR,wireBlock_length] using hv) s m
  exact ⟨hp,stepT w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.2.2.1,hcv s.basis h])⟩

theorem stepCCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (a b : Wire) (j : Nat)
    (hj : j=721 ∨ j=722) (av bv : Bool) (ha : a≠w j) (hb : b≠w j)
    (hav : ∀s : BasisState,MF w b0 H X T par f gp fp s → s a=av)
    (hbv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s b=bv) :
    Triple (MF w b0 H X T par f gp fp) [.CCX a b (w j)]
      (MF w b0 H X T par f (if j=721 then gp ^^ (av && bv) else gp)
        (if j=722 then fp ^^ (av && bv) else fp)) := by
  intro s m h
  rw [run_ccx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w j)
    (s.basis (w j) ^^ (s.basis a && s.basis b))⟩ j (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  rcases hj with rfl|rfl
  · simpa [writeBit,h.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this
  · simpa [writeBit,h.2.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this

theorem stepKAdd (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 H X T par f gp fp) (kAddM w) (MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m h
  have caway : ∀q∈aC w,q∉mutL w := by
    intro q hq hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
    · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
    all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm
  have m1797 : w 1797∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have nd : (w 1797::(kR w++aC w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),
      blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
  have src : ∀q∈mappedWires (mappedRead (hR w) false),q∉w 1797::(kR w++aC w) := by
    rw [mappedRead_wires]
    intro q hq hm
    simp only [List.mem_cons,List.mem_append] at hm
    rcases hm with e|e|e
    · exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq)
    · exact hR_kR w hn q e hq
    · exact List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq e
  have cl : ∀q∈aC w,s.basis q=false := fun q hq => (h.2.2.2.2.2.2.2 q (caway q hq)).trans (hc q hq)
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (mappedRead (hR w) false) (kR w) (aC w) (w 1797) nd src
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length]) s m cl
  refine ⟨hp,stepK w hn b0 H X T par f gp fp s _ h he _ ?_⟩
  rw [hval,mappedRead_value,h.1,h.2.1,(h.2.2.2.2.2.2.2 _ m1797).trans hcin]
  simp [kR,wireBlock_length]

end Concrete2


def CF (w : Nat → Wire) (b0 : BasisState) (S : Nat) (F : Bool) (s : BasisState) : Prop :=
  regValue (srcR w) s=S ∧ s (w 514)=F ∧ ∀q,q∉srcR w → q≠w 514 → s q=b0 q

section Compare
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem src_nd : (srcR w).Nodup := blk_nd w hn 0 256 (by omega)
theorem w514_src : w 514∉srcR w := nb w hn 514 0 256 (by omega) (by omega) (by omega)

theorem cfMask (b0 : BasisState) (S : Nat) (F : Bool) (c : Wire) (hc : c∉srcR w) (hc' : c≠w 514)
    (v : Nat) (hv : v<2^256) :
    Triple (CF w b0 S F) (maskedConstant c (srcR w) v) (CF w b0 (S^^^(if b0 c then v else 0)) F) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (srcR w) v (src_nd w hn) hc
    (by simpa [srcR,wireBlock_length] using hv) s m
  refine ⟨hp,?_,?_,?_⟩
  · rw [hval,h.1,h.2.2 c hc hc']
  · rw [he _ (w514_src w hn)]; exact h.2.1
  · intro q h1 h2; rw [he q h1]; exact h.2.2 q h1 h2

theorem cfNot (b0 : BasisState) (S : Nat) (F : Bool) :
    Triple (CF w b0 S F) (notRegister (srcR w)) (CF w b0 (2^256-1-S) F) := by
  intro s m h
  rw [notRegister_correct (srcR w) (src_nd w hn)]
  refine ⟨rfl,?_,?_,?_⟩
  · change regValue (srcR w) (fun q => if q∈srcR w then !s.basis q else s.basis q)=_
    rw [regValue_congr (srcR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,h.1]
    simp [srcR,wireBlock_length]
  · change (if w 514∈srcR w then !s.basis (w 514) else s.basis (w 514))=_
    simp [w514_src w hn,h.2.1]
  · intro q h1 h2
    change (if q∈srcR w then !s.basis q else s.basis q)=_
    simp [h1,h.2.2 q h1 h2]

theorem cfCmp (b0 : BasisState) (S : Nat) (F : Bool) (X : Nat) (hx : regValue (xR w) b0=X)
    (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false) :
    Triple (CF w b0 S F) (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514))
      (CF w b0 S (F ^^ decide (S<X))) := by
  intro s m h
  have xs : ∀q∈xR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)) h' hq
  have x514 : ∀q∈xR w,q≠w 514 := fun q hq e => nb w hn 514 770 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have cs : ∀q∈cR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)) h' hq
  have c514 : ∀q∈cR w,q≠w 514 := fun q hq e => nb w hn 514 256 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have n513 : w 513∉srcR w := nb w hn 513 0 256 (by omega) (by omega) (by omega)
  have e513 : w 513≠w 514 := w_ne w hn 513 514 (by omega) (by omega) (by omega)
  have nd : (w 514::w 513::(srcR w++xR w++cR w)).Nodup := by
    have a1 := blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
    have l1 : (srcR w++xR w).Nodup := List.nodup_append'.mpr ⟨src_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
    have l2 : (srcR w++xR w++cR w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨e513.symm,⟨w514_src w hn,nb w hn 514 770 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨n513,nb w hn 513 770 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hv⟩ := compareLt_correct none (srcR w) (xR w) (cR w) (w 513) (w 514) nd (by simp)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,xR,wireBlock_length]) s m
    ((h.2.2 _ n513 e513).trans hcin) (fun q hq => (h.2.2 q (cs q hq) (c514 q hq)).trans (hc q hq))
  refine ⟨hp,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => he q (fun e => w514_src w hn (e ▸ hq)))]; exact h.1
  · rw [hv,h.2.1,h.1,regValue_congr _ _ b0 (fun q hq => h.2.2 q (xs q hq) (x514 q hq)),hx]
    simp [controlValue]
  · intro q h1 h2; rw [he q h2]; exact h.2.2 q h1 h2

theorem cfCompare (b0 : BasisState) (F : Bool) (k X : Nat) (hk : cmpC+k<2^256)
    (hx : regValue (xR w) b0=X) (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) :
    Triple (CF w b0 0 F) (comparePart w g k)
      (CF w b0 0 (F ^^ decide (2^256-1-(if b0 g then cmpC+k else 0)<X))) := by
  have t := ((((cfMask w hn b0 0 F g gs g514 (cmpC+k) hk).seq
    (cfNot w hn b0 _ F)).seq (cfCmp w hn b0 _ F X hx hc hcin)).seq
    (cfNot w hn b0 _ _)).seq (cfMask w hn b0 _ _ g gs g514 (cmpC+k) hk)
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have lt : (if b0 g then cmpC+k else 0)<2^256 := by split <;> omega
  refine ⟨?_,?_,h.2.2⟩
  · rw [h.1]
    have e : 2^256-1-(2^256-1-(0^^^(if b0 g then cmpC+k else 0)))=(if b0 g then cmpC+k else 0) := by
      simp only [Nat.zero_xor]; omega
    rw [e,Nat.xor_self]
  · rw [h.2.1]; simp only [Nat.zero_xor]

end Compare


def dScalar (par : Bool) : Nat :=
  (List.range 257).foldr (fun j acc => (if par then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0

theorem dScalar_value (par : Bool) : dScalar par=delta par := by
  cases par <;> decide

private theorem selected_bit_value (flag : Wire) (a b : Bool) (s : BasisState) :
    (if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a}).value s=if s flag then b else a := by
  cases a <;> cases b <;> cases hf : s flag <;> simp [MappedBit.value,hf]

private theorem d_list_value (is : List Nat) (flag : Wire) (s : BasisState) :
    mappedValue (is.map (fun j =>
      let a := (2^257-p).testBit j
      let b := p.testBit j
      if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some flag,flip:=a})) s=
      is.foldr (fun j acc => (if s flag then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih,selected_bit_value]

theorem dBits_value (w : Nat → Wire) (s : BasisState) : mappedValue (dBits w) s=delta (s (w 1028)) := by
  rw [dBits,d_list_value]
  exact dScalar_value (s (w 1028))

theorem dBits_length (w : Nat → Wire) : (dBits w).length=257 := by simp [dBits]

theorem dBits_cons (w : Nat → Wire) :
    ∃ b' bs, dBits w = {wire:=none,flip:=true} :: b' :: bs := by
  have e : List.range 257 = 0 :: 1 :: List.range' 2 255 := by
    rw [List.range_eq_range']; rfl
  have t1 : (2^257-p).testBit 0 = true := by rw [p_val]; decide
  have t2 : p.testBit 0 = true := by rw [p_val]; decide
  rw [dBits, e, List.map_cons, List.map_cons]
  simp only [t1, t2, ite_true]
  exact ⟨_, _, rfl⟩

theorem hpR_cons (w : Nat → Wire) : ∃ y' ys, hpR w = w 1 :: y' :: ys :=
  ⟨w 2, (List.range' 3 255).map w, by
    rw [hpR, wireBlock, show (257:Nat) = 255+1+1 from rfl, List.range'_succ, List.range'_succ]; rfl⟩

theorem hC2_cons (w : Nat → Wire) : ∃ cs, hC2 w = w 1540 :: cs :=
  ⟨(List.range' 1541 255).map w, by
    rw [hC2, wireBlock, show (256:Nat) = 255+1 from rfl, List.range'_succ]; rfl⟩

theorem hAddM_split (w : Nat → Wire) :
    hAddM w = [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ [.CCX (w 1) (w 1797) (w 1540)] ++ hPost w := by
  obtain ⟨b', bs, hD⟩ := dBits_cons w
  obtain ⟨y', ys, hY⟩ := hpR_cons w
  obtain ⟨cs, hC⟩ := hC2_cons w
  simp only [hAddM, hPost, hD, hY, hC, List.tail_cons, mappedAdd, mappedMajority, List.append_assoc,
    List.cons_append, List.nil_append, if_true]

/-- Dropping a Toffoli whose second control is false after a measurement-free prefix. -/
theorem run_drop_ccx (P Q : Program) (a b t : Wire) (m : List Bool) (s : State)
    (hP : measurementCount P = 0) (hb : (run P [] s).basis b = false) :
    run (P ++ [.CCX a b t] ++ Q) m s = run (P ++ Q) m s := by
  rw [List.append_assoc, run_append, run_append P Q, hP]
  simp only [List.take_zero, List.drop_zero, List.cons_append, List.nil_append, run, hb,
    Bool.and_false, Bool.xor_false, writeBit, Function.update_eq_self]

theorem hAddT_run (w : Nat → Wire) (h17 : w 1797 ≠ w 1540) (m : List Bool) (s : State)
    (hc : s.basis (w 1797) = false) : run (hAddT w) m s = run (hAddM w) m s := by
  rw [hAddM_split, hAddT, run_drop_ccx]
  · rfl
  · simp only [run, writeBit, Function.update_of_ne h17, hc]

theorem hAddT_counts (w : Nat → Wire) :
    toffoliCount (hAddT w) + 1 = toffoliCount (hAddM w) ∧
      measurementCount (hAddT w) = measurementCount (hAddM w) := by
  rw [hAddM_split, hAddT]
  simp only [toffoliCount_append, measurementCount_append]
  constructor
  · simp [toffoliCount]; omega
  · simp [measurementCount]

theorem hAddT_wires (w : Nat → Wire) : wires (hAddT w) ⊆ wires (hAddM w) := by
  rw [hAddM_split, hAddT]
  simp only [wires_append]
  exact Finset.union_subset_union (Finset.subset_union_left) (Finset.Subset.refl _)

theorem hAddT_physical (w : Nat → Wire) (h : GatePhysical (hAddM w)) : GatePhysical (hAddT w) := by
  rw [hAddM_split] at h
  rw [hAddT]
  simp only [gatePhysical_append] at h ⊢
  exact ⟨h.1.1, h.2⟩

theorem hAddT_slots (w : Nat → Wire) :
    Challenge.gateSlots (hAddT w) + 1 = Challenge.gateSlots (hAddM w) := by
  rw [hAddM_split, hAddT]
  simp only [Challenge.gateSlots_append]
  simp [Challenge.gateSlots, Challenge.instructionSlots]
  omega


theorem dBits_wire (w : Nat → Wire) (q : Wire) (hq : q∈mappedWires (dBits w)) : q=w 1028 := by
  simp only [dBits,mappedWires,List.mem_flatMap,List.mem_map] at hq
  obtain ⟨b,⟨j,_,rfl⟩,hb⟩ := hq
  split at hb <;> simp_all

section Rest
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepCompareMF (b0 : BasisState) (k X : Nat) (hk : cmpC+k<2^256) (hX : X<2^256)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) (gm : g∉mutL w) :
    Triple (MF w b0 0 X 0 false false false false) (comparePart w g k)
      (MF w b0 0 X 0 false (decide (2^256-1-(if b0 g then cmpC+k else 0)<X)) false false) := by
  intro s m h
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have sp := hR_src w hn s.basis
  have kx := kR_x w hn s.basis
  have xl := regValue_lt (xR w) s.basis
  have sl := regValue_lt (srcR w) s.basis
  simp only [xR,srcR,wireBlock_length] at xl sl
  rw [h1] at sp; rw [h2] at kx
  have hx : regValue (xR w) s.basis=X := by
    have : regValue (wireBlock w 1026 2) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 1026 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 1026 2) s.basis := Nat.le_mul_of_pos_right _ this
      omega
    omega
  have src0 : regValue (srcR w) s.basis=0 := by omega
  have top0 : regValue (wireBlock w 256 2) s.basis=0 := by
    by_contra hne; have : 1≤regValue (wireBlock w 256 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
    have : 2^256≤2^256*regValue (wireBlock w 256 2) s.basis := Nat.le_mul_of_pos_right _ this
    omega
  have hzero := (regValue_zero _ _).mp h1
  have cc : ∀q∈cR w,s.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    by_cases hi2 : i<258
    · exact hzero _ ((mem_blk w hn i 0 258 (by omega) (by omega)).mpr (by omega))
    · rw [h8 _ ?_]; exact hc i (by omega) (by omega)
      simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
      refine ⟨⟨⟨nb w hn i 0 258 (by omega) (by omega) (by omega),nb w hn i 770 258 (by omega) (by omega) (by omega)⟩,
        nb w hn i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
        exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have m513 : w 513∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 513 0 258 (by omega) (by omega) (by omega),nb w hn 513 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 513 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have cfr := cfCompare w g hn s.basis false k X hk hx cc ((h8 _ m513).trans hcin) gs g514 s m
    ⟨src0,h5,fun _ _ _ => rfl⟩
  obtain ⟨tp,c1',c2',c3'⟩ := cfr
  refine ⟨tp,?_⟩
  simp only [Bool.false_xor] at c2'
  have gv : s.basis g=b0 g := h8 g gm
  rw [gv] at c2'
  have same : ∀q,q∉srcR w → q≠w 514 → (run (comparePart w g k) m s).basis q=s.basis q := c3'
  have srcm : ∀q∈srcR w,q∈mutL w := fun q hq => hR_mut w hn q (blk_sub w 0 256 0 258 (by omega) (by omega) q hq)
  have m514 : w 514∈mutL w := by simp [mutL]
  refine ⟨?_,?_,?_,?_,c2',?_,?_,?_⟩
  · rw [hR_src w hn,c1',regValue_congr _ _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 256 2 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 256 2 (by omega) (by omega) (by omega) (e ▸ hq))),top0]; simp
  · rw [regValue_congr (kR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 770 258 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 770 258 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h2
  · rw [regValue_congr (tR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 1029 256 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 1029 256 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h3
  · rw [same _ (nb w hn 1028 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h4
  · rw [same _ (nb w hn 721 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h6
  · rw [same _ (nb w hn 722 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h7
  · intro q hq
    rw [same q (fun h' => hq (srcm q h')) (fun e => hq (e ▸ m514))]; exact h8 q hq

theorem stepMeasFp (b0 : BasisState) (H X T : Nat) (par f gp : Bool) :
    Triple (MF w b0 H X T par f gp (f && par)) [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]
      (MF w b0 H X T par f gp false) := by
  intro s m h
  rw [run_meas_and (w 722) (w 514) (w 1028) m s (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.2.1,h.2.2.2.2.1,h.2.2.2.1])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp (f && par) s ⟨s.phase,writeBit s.basis (w 722) false⟩ 722
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepMeasGp (b0 : BasisState) (H X T : Nat) (par f fp : Bool) (gm : g∉mutL w)
    (g515 : g≠w 721) :
    Triple (MF w b0 H X T par f (b0 g && par) fp) [.measureX (w 721) [] [.CZ g (w 1028)]]
      (MF w b0 H X T par f false fp) := by
  intro s m h
  rw [run_meas_and (w 721) g (w 1028) m s g515
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.1,h.2.2.2.1,h.2.2.2.2.2.2.2 g gm])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f (b0 g && par) fp s ⟨s.phase,writeBit s.basis (w 721) false⟩ 721
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepCopy (b0 : BasisState) (X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 X T par f gp fp) (copyRegister none (wireBlock w 770 257) (hpR w))
      (MF w b0 (2*(X%2^257)) X T par f gp fp) := by
  intro s m h
  have nd : (wireBlock w 770 257++hpR w).Nodup := List.nodup_append'.mpr
    ⟨blk_nd w hn 770 257 (by omega),blk_nd w hn 1 257 (by omega),
      blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hval⟩ := copyRegister_correct none (wireBlock w 770 257) (hpR w)
    (by simp [hpR,wireBlock_length]) nd (by simp) s m
  refine ⟨hp,stepH w hn b0 0 X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (copyRegister none (wireBlock w 770 257) (hpR w)) m s).basis
    have kl := kR_low w hn s.basis
    have ll := regValue_lt (wireBlock w 770 257) s.basis
    simp only [wireBlock_length] at ll
    rw [h.1] at sp; rw [h.2.1] at kl
    rw [sp2,hval,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega))]
    simp only [copyValue]
    have e0 : regValue (hpR w) s.basis=0 := by omega
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    rw [e0,b0',Nat.zero_xor]
    have : regValue (wireBlock w 770 257) s.basis=X%2^257 := by omega
    rw [this]; simp

end Rest


section Rest2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem aC_out : ∀q∈aC w,q∉mutL w := by
  intro q hq hm
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
  · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
  all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm

theorem w1797_out : w 1797∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
    nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
    exact w_ne w hn _ _ (by omega) (by omega) (by omega)

theorem stepHAdd (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddM w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  rw [hAddM]
  have nd : (w 1797::(hpR w++hC2 w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),
      blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
  have srcw : ∀q∈mappedWires (dBits w),q∉w 1797::(hpR w++hC2 w) := by
    intro q hq
    rw [dBits_wire w q hq]
    simp only [List.mem_cons,List.mem_append,not_or]
    exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
      nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC2 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 256 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (dBits w) (hpR w) (hC2 w) (w 1797) nd srcw
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length]) s m cl
  refine ⟨hp,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)) m s).basis
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have e0 : regValue (hpR w) s.basis=Y := by rw [b0'] at sp; simp at sp; omega
    rw [sp2,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega)),b0',hval,dBits_value,e0,
      h.2.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin]
    simp [hpR,wireBlock_length]

theorem stepHAddT (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddT w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  have c17 : s.basis (w 1797)=false := (h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin
  rw [hAddT_run w (w_ne w hn 1797 1540 (by omega) (by omega) (by omega)) m s c17]
  exact stepHAdd w hn b0 Y X T par f gp fp hY hc hcin s m h

theorem stepW0 (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 (2*Y) X T par f gp fp) [.CX (w 1028) (w 0),.X (w 0)]
      (MF w b0 (2*Y+(!par).toNat) X T par f gp fp) := by
  intro s m h
  have e : run [.CX (w 1028) (w 0),.X (w 0)] m s=⟨s.phase,writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028)))⟩ := by
    simp [run,writeBit]
  rw [e]
  refine ⟨rfl,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq
    have : q≠w 0 := fun e' => hq (e' ▸ (mem_blk w hn 0 0 258 (by omega) (by omega)).mpr (by omega))
    simp [writeBit,Function.update_of_ne this]
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have rest : regValue (hpR w) (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))=
        regValue (hpR w) s.basis := regValue_congr _ _ _ (fun q hq => by
      have : q≠w 0 := fun e' => nb w hn 0 1 257 (by omega) (by omega) (by omega) (e' ▸ hq)
      simp [writeBit,Function.update_of_ne this])
    rw [sp2,rest,b0',h.2.2.2.1]
    rw [b0'] at sp
    simp [writeBit] at sp ⊢
    omega

theorem stepErase (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) (hH : H<2^257) (hf : f=decide (H/2<T)) :
    Triple (MF w b0 H X T par f gp fp) (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))
      (MF w b0 H X T par false gp fp) := by
  intro s m h
  have nd : (w 514::w 1797::(hp8 w++tR w++hC3 w)).Nodup := by
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),⟨nb w hn 514 1 256 (by omega) (by omega) (by omega),
        nb w hn 514 1029 256 (by omega) (by omega) (by omega)⟩,nb w hn 514 1540 255 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC3 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 255 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have sp := hR_split w hn s.basis
  rw [h.1] at sp
  have e8 : hpR w=hp8 w++wireBlock w 257 1 := by rw [hpR,hp8,wireBlock_append]
  have sp8 := regValue_append (hp8 w) (wireBlock w 257 1) s.basis
  rw [←e8] at sp8
  have l8 := regValue_lt (hp8 w) s.basis
  simp only [hp8,wireBlock_length] at sp8 l8
  have hpv : regValue (hp8 w) s.basis=H/2 := by
    have : regValue (wireBlock w 257 1) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 257 1) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 257 1) s.basis := Nat.le_mul_of_pos_right _ this
      cases hb : s.basis (w 0) <;> simp [hb] at sp <;> omega
    cases hb : s.basis (w 0) <;> simp [hb] at sp <;> simp only [hp8] at * <;> omega
  have r := eraseLtChain_correct (hp8 w) (tR w) (hC3 w) (w 1797) (w 514) nd
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length]) s m cl
    (by rw [h.2.2.2.2.1,hpv,h.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin,hf]; simp)
  rw [r]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 514) false⟩ 514
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

end Rest2


section Compose
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem g_mut (hg : g∉skywalkPoolWires w) : g∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨g_out w hn g hg 0 258 (by omega),g_out w hn g hg 770 258 (by omega)⟩,g_out w hn g hg 1029 256 (by omega)⟩,
    g_ne w hn g hg 1028 (by omega),g_ne w hn g hg 514 (by omega),g_ne w hn g hg 721 (by omega),g_ne w hn g hg 722 (by omega)⟩

theorem low_bit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState)
    (h : MF w b0 H X T par f gp fp s) : s (w 770)=decide (X%2=1) := by
  have sp := kR_split w hn s
  rw [h.2.1] at sp
  cases hb : s (w 770) <;> simp [hb] at sp ⊢ <;> omega

omit hn in
theorem xor_clear (a b c : Bool) : (((a ^^ (((false ^^ a) ^^ b) ^^ c)) ^^ b) ^^ c)=false := by
  cases a <;> cases b <;> cases c <;> rfl
omit hn in
theorem xor_clear2 (a c : Bool) : ((a ^^ ((false ^^ a) ^^ c)) ^^ c)=false := by
  cases a <;> cases c <;> rfl

theorem stepPar (b0 : BasisState) (k X : Nat) (f : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 0 X 0 false f false false) (parGates w g k)
      (MF w b0 0 (2*(X/2)) 0 (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f) f false false) := by
  have gm := g_mut w g hn hg
  have g1028 : g≠w 1028 := g_ne w hn g hg 1028 (by omega)
  have g770 : g≠w 770 := g_ne w hn g hg 770 (by omega)
  have e1 : w 770≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e2 : w 514≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e3 : w 1028≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e4 : w 514≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have gv (H X T : Nat) (par f gp fp : Bool) : ∀s : BasisState,MF w b0 H X T par f gp fp s → s g=b0 g :=
    fun s h => h.2.2.2.2.2.2.2 g gm
  have xs : X=2*(X/2)+(decide (X%2=1)).toNat := by
    rcases Nat.mod_two_eq_zero_or_one X with hx|hx <;> simp [hx] <;> omega
  apply Triple.conseq (fun s h => by rw [xs] at h; exact h) ?_ (fun s h => h)
  by_cases hk : k%2=1
  · rw [parGates,if_pos hk,if_pos hk]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false g (b0 g) g1028 (gv _ _ _ _ _ _ _)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 _ _ f false false g (b0 g) g770 (gv _ _ _ _ _ _ _)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear] at h
    simpa [hk] using h
  · rw [parGates,if_neg hk,if_neg hk]
    try simp only [List.nil_append]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear2] at h
    simpa [hk] using h

theorem stepRot (b0 : BasisState) (X : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 (2*(X/2)) 0 par f gp fp) (rotateRight (kR w)) (MF w b0 0 (X/2) 0 par f gp fp) := by
  intro s m h
  have r := rotateRight_spec (kR w) (kR_nd w hn) (2*(X/2)) (by omega) s m h.2.1
  have fr := rotate_frame (kR w) s m
  refine ⟨r.1,stepK w hn b0 0 _ 0 par f gp fp s _ h fr.2.1 _ ?_⟩
  have := r.2
  change regValue (kR w) _=_ at this
  rw [this]; omega

end Compose


theorem kC_lt (par : Bool) : kConstant false par<2^258 := by
  cases par <;> norm_num [kConstant,ECDSAAdd.p]

theorem tk_lt (k : Nat) (G f par : Bool) : tk k G f par<2^258 := by
  unfold tk
  split_ifs
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num
  · exact Nat.mod_lt _ (by norm_num)
  · exact kC_lt par

theorem xlt (a b : Nat) (ha : a<2^258) (hb : b<2^258) : a^^^b<2^258 := Nat.xor_lt_two_pow ha hb

theorem c1_lt (k : Nat) : c1 k<2^258 := tk_lt k _ _ _
theorem cg_lt (k : Nat) : cg k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cf_lt (k : Nat) : cf k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cp_lt (k : Nat) : cp k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cgp_lt (k : Nat) : cgp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)
theorem cfp_lt (k : Nat) : cfp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)

def lkv (k : Nat) (G f par gp fp : Bool) : Nat :=
  c1 k ^^^ (if G then cg k else 0) ^^^ (if f then cf k else 0) ^^^ (if par then cp k else 0) ^^^
    (if gp then cgp k else 0) ^^^ (if fp then cfp k else 0)

theorem lkv_eq (k : Nat) (G f par : Bool) (hfg : f=true → G=true) :
    lkv k G f par (G && par) (f && par)=tk k G f par := by
  cases G <;> cases f <;> cases par <;> simp at hfg <;>
    simp [lkv,c1,cg,cf,cp,cgp,cfp,Nat.xor_assoc,Nat.xor_comm,Nat.xor_left_comm,Nat.xor_self]

def ltv (k : Nat) (G gp : Bool) : Nat := (if G then thrA k else 0) ^^^ (if gp then thrB k else 0)

theorem ltv_eq (k : Nat) (G par : Bool) : ltv k G (G && par)=thr k G par := by
  cases G <;> cases par <;> simp [ltv,thr,thrA,thrB,Nat.xor_assoc,Nat.xor_self]

section Compose2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepLoadK (b0 : BasisState) (k H X T : Nat) (par f gp fp : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadK w g k)
      (MF w b0 (H^^^lkv k (b0 g) f par gp fp) X T par f gp fp) := by
  have gm := g_mut w g hn hg
  have gh : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h515 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h516 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t := (stepXorH w hn b0 H X T par f gp fp (c1 k) (c1_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp g (b0 g) gh (fun s h => h.2.2.2.2.2.2.2 g gm) (cg k) (cg_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 514) f h514 (fun s h => h.2.2.2.2.1) (cf k) (cf_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 1028) par h1028 (fun s h => h.2.2.2.1) (cp k) (cp_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (cgp k) (cgp_lt k)).seq
    (stepMaskH w hn b0 _ X T par f gp fp (w 722) fp h516 (fun s h => h.2.2.2.2.2.2.1) (cfp k) (cfp_lt k))))))
  unfold loadK
  simp only [List.append_assoc]
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have e : H^^^c1 k^^^(if b0 g then cg k else 0)^^^(if f then cf k else 0)^^^(if par then cp k else 0)^^^
      (if gp then cgp k else 0)^^^(if fp then cfp k else 0)=H^^^lkv k (b0 g) f par gp fp := by
    simp only [lkv,Nat.xor_assoc]
  rw [e] at h; exact h

theorem stepLoadT (b0 : BasisState) (k H X T : Nat) (hk : k<p) (par f gp fp : Bool)
    (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadT w g k)
      (MF w b0 H X (T^^^ltv k (b0 g) gp) par f gp fp) := by
  have gm := g_mut w g hn hg
  have gt : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have h515 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  rw [p_val] at hk
  have la : thrA k<2^256 := by unfold thrA; omega
  have lb : thrB k<2^256 := Nat.xor_lt_two_pow la (by rw [p_val]; omega)
  have t := (stepMaskT w hn b0 H X T par f gp fp g (b0 g) gt (fun s h => h.2.2.2.2.2.2.2 g gm) (thrA k) la).seq
    (stepMaskT w hn b0 H X _ par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (thrB k) lb)
  unfold loadT
  apply Triple.conseq (fun _ h => h) t
  intro s h
  simpa only [ltv,Nat.xor_assoc] using h

end Compose2


section Main
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (hac : ∀q∈aC w,b0 q=false) (h1797 : b0 (w 1797)=false) :
    let G := b0 g
    let f := decide (2^256-1-(if G then 2^256-p+k else 0)<X)
    let dx := (X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    Triple (MF w b0 0 X 0 false false false false) (merged w g k)
      (MF w b0 (2*H+(!par).toNat) K 0 par false false false) := by
  intro G f dx par K H
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX G
  change decide (X%2=1)=x0 k G f par at a1
  change (X/2+tk k G f par)%2^258=K at a2
  change H=dx/2+(if par then hConstant else 0) at a3
  change f=decide (H<thr k G par) at a4
  have gm := g_mut w g hn hg
  have hp' := p_val
  have hpar : (decide (X%2=1) ^^ (G && decide (k%2=1)) ^^ f)=par := by
    have e : decide (X%2=1)=x0 k G f par := a1
    rw [e]; unfold x0 ksel0
    generalize (G && decide (k%2=1))=a
    cases par <;> cases a <;> cases f <;> rfl
  have hfg : f=true → G=true := by
    intro hf; cases hG : G
    · have : f=false := by
        simp only [f,hG,Bool.false_eq_true,if_false,decide_eq_false_iff_not]; rw [p_val] at hX; omega
      rw [this] at hf; exact absurd hf (by simp)
    · rfl
  have fC : decide (2^256-1-(if b0 g then cmpC+k else 0)<X)=f := by simp [f,G,cmpC]
  have s1 := stepCompareMF w g hn b0 k X (by unfold cmpC; rw [p_val] at hk ⊢; omega) (by rw [p_val] at hX; omega)
    hc hcin (g_out w hn g hg 0 256 (by omega)) (g_ne w hn g hg 514 (by omega)) gm
  rw [fC] at s1
  have s2 := stepPar w g hn b0 k X f hg
  rw [show (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f)=par from hpar] at s2
  have s3 := stepRot w hn b0 X par f false false
  have s4a := stepCCX w hn b0 0 (X/2) 0 par f false false g (w 1028) 721 (by omega) G par
    (g_ne w hn g hg 721 (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 g gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s4a
  have s4b := stepCCX w hn b0 0 (X/2) 0 par f (G && par) false (w 514) (w 1028) 722 (by omega) f par
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s4b
  have s5 := stepLoadK w g hn b0 k 0 (X/2) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 g=G from rfl,lkv_eq k G f par hfg] at s5
  have s6 := stepKAdd w hn b0 (tk k G f par) (X/2) 0 par f (G && par) (f && par) hac h1797
  rw [show (tk k G f par+X/2)%2^258=K by rw [Nat.add_comm]; exact a2] at s6
  have s7 := stepLoadK w g hn b0 k (tk k G f par) K 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkv_eq k G f par hfg,Nat.xor_self] at s7
  have s8 := stepMeasFp w hn b0 0 K 0 par f (G && par)
  have s9 := stepCopy w hn b0 K 0 par f (G && par) false
  have s10 := stepHAddT w hn b0 (K%2^257) K 0 par f (G && par) false (Nat.mod_lt _ (by norm_num)) hac h1797
  rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]] at s10
  have s11 := stepW0 w hn b0 H K 0 par f (G && par) false
  have s12 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K 0 hk par f (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltv_eq] at s12
  have hHlt : 2*H+(!par).toNat<2^257 := by
    have dxl : dx<p := Nat.mod_lt _ (by rw [p_val]; norm_num)
    rw [a3]; rw [p_val] at dxl
    cases par <;> simp [hC_val] <;> omega
  have s13 := stepErase w hn b0 (2*H+(!par).toNat) K (thr k G par) par f (G && par) false hac h1797 hHlt
    (by rw [show (2*H+(!par).toNat)/2=H by cases par <;> simp <;> omega]; exact a4)
  have s14 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K (thr k G par) hk par false (G && par) false hg
  rw [show b0 g=G from rfl,ltv_eq,Nat.xor_self] at s14
  have s15 := stepMeasGp w g hn b0 (2*H+(!par).toNat) K 0 par false false gm (g_ne w hn g hg 721 (by omega))
  have t := s1.seq (s2.seq (s3.seq (s4a.seq (s4b.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    (s11.seq (s12.seq (s13.seq (s14.seq s15))))))))))))))
  unfold merged prodPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

end Main


section Final
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

/-- The merged circuit leaves exactly the state of the old compare-first constant addition
followed by the direct first tick, on every measurement record. -/
theorem merged_eq_forward (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (t u : State) (m m' : List Bool)
    (tk0 : regValue (kR w) t.basis=X) (th0 : regValue (hR w) t.basis=0) (tt0 : regValue (tR w) t.basis=0)
    (t1028 : t.basis (w 1028)=false) (t514 : t.basis (w 514)=false) (t515 : t.basis (w 721)=false)
    (t516 : t.basis (w 722)=false)
    (hc : ∀ i, 258 ≤ i → i < 512 → t.basis (w i) = false) (hcin : t.basis (w 513)=false)
    (hac : ∀q∈aC w,t.basis q=false) (h1797 : t.basis (w 1797)=false)
    (hu : u.phase=t.phase) (hu2 : ∀q,q∉kR w → u.basis q=t.basis q)
    (hu3 : regValue (kR w) u.basis=(X+(if t.basis g then k else 0))%p) :
    run (merged w g k) m t=run (NativeFirstDirect.forward w) m' u := by
  have mf0 : MF w t.basis 0 X 0 false false false false t.basis :=
    ⟨th0,tk0,tt0,t1028,t514,t515,t516,fun _ _ => rfl⟩
  have tri := merged_triple w g hn hg k hk t.basis X hX hc hcin hac h1797 t m mf0
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX (t.basis g)
  generalize hG : t.basis g=G at tri a1 a2 a3 a4 a5 hu3
  generalize hdx : (X+(if G then k else 0))%p=dx at tri a1 a2 a3 a4 a5 hu3
  generalize hpar : decide (dx%2=1)=par at tri a1 a2 a3 a4 a5
  generalize hK : (dx/2+kConstant false par)%2^258=K at tri a1 a2 a3 a4 a5
  generalize hH : (K%2^257+delta par)%2^257=H at tri a1 a2 a3 a4 a5
  obtain ⟨lp,l1,l2,l3,l4,l5,l6,l7,l8⟩ := tri
  have dxlt : dx<p := by rw [←hdx]; exact Nat.mod_lt _ (by rw [p_val]; norm_num)
  have kh : ∀q∈hR w,q∉kR w := kR_hR w hn
  have kt : ∀q∈tR w,q∉kR w := kR_tR w hn
  have hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 dx u.basis := by
    constructor
    · change regValue (wireBlock w 0 258) u.basis=0
      rw [show wireBlock w 0 258=hR w from rfl,regValue_congr _ _ t.basis (fun q hq => hu2 q (kh q hq)),th0]
    · change regValue (wireBlock w 770 258) u.basis=dx
      exact hu3
    · change regValue (wireBlock w 1540 257) u.basis=0
      apply (regValue_zero _ _).mpr
      intro q hq
      rw [hu2 q (fun h' => List.disjoint_left.mp (blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)) h' hq)]
      exact hac q hq
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
    · change u.basis (w 1028)=false
      rw [hu2 _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact t1028
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec w hn dx dxlt u m' hin
  have e770 : u.basis (w 770)=par := by
    have sp := kR_split w hn u.basis
    rw [hu3] at sp
    rw [←hpar]
    cases hb : u.basis (w 770) <;> simp [hb] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  rw [hK] at zk
  have hv : 2*(dx/2+(if par then hConstant else 0))+(!par).toNat=2*H+(!par).toNat := by rw [a3]
  rw [hv] at zh
  apply State.extensionality
  · rw [lp,zp,hu]
  · funext q
    by_cases qh : q∈hR w
    · exact (regValue_eq_iff (hR w) _ _).mp (l1.trans zh.symm) q qh
    by_cases qk : q∈kR w
    · exact (regValue_eq_iff (kR w) _ _).mp (l2.trans zk.symm) q qk
    by_cases q1 : q=w 1028
    · rw [q1,l4,z1028]
    have nmut : q∉NativeFirstDirect.mutable w := by
      simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
      exact ⟨⟨fun h' => qh (blk_sub w 0 257 0 258 (by omega) (by omega) q h'),qk⟩,q1⟩
    rw [zrest q nmut,hu2 q qk]
    by_cases qt : q∈tR w
    · rw [(regValue_zero _ _).mp l3 q qt,(regValue_zero _ _).mp tt0 q qt]
    by_cases q4 : q=w 514
    · rw [q4,l5,t514]
    by_cases q5 : q=w 721
    · rw [q5,l6,t515]
    by_cases q6 : q=w 722
    · rw [q6,l7,t516]
    apply l8
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,qk⟩,qt⟩,q1,q4,q5,q6⟩

end Final


/-! ### Resources -/

def mSites (w : Nat → Wire) (g : Wire) : List Wire :=
  wireBlock w 0 515++wireBlock w 770 515++wireBlock w 1540 258++[w 721,w 722,g]

theorem in_mSites (w : Nat → Wire) (g : Wire) (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) : w i∈mSites w g := by
  simp only [mSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hi with h|h|h|h|h
  · exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩))
  · subst h; exact Or.inr (Or.inl rfl)
  · subst h; exact Or.inr (Or.inr (Or.inl rfl))

theorem blk_mSites (w : Nat → Wire) (g : Wire) (a n : Nat)
    (h : a + n ≤ 515 ∨ (770 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
    ∀q∈wireBlock w a n,q∈mSites w g := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact in_mSites w g i (by omega)

theorem g_mSites (w : Nat → Wire) (g : Wire) : g∈mSites w g := by simp [mSites]

theorem dBits_wires_sub (w : Nat → Wire) : ∀q∈mappedWires (dBits w),q=w 1028 := dBits_wire w

theorem lsub (w : Nat → Wire) (g : Wire) (l : List Wire) (h : ∀q∈l,q∈mSites w g) :
    l.toFinset⊆(mSites w g).toFinset := by
  intro q hq; exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem gate_sub (w : Nat → Wire) (g : Wire) (i : Instr) (h : ∀q∈i.wires,q∈mSites w g) :
    wires [i]⊆(mSites w g).toFinset := by
  intro q hq
  simp only [wires,Finset.union_empty] at hq
  exact List.mem_toFinset.mpr (h q hq)

theorem merged_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (merged w g k)⊆(mSites w g).toFinset := by
  have B := blk_mSites w g
  have I := in_mSites w g
  have G := g_mSites w g
  have mskH (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have mskS (v : Nat) : wires (maskedConstant g (srcR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset g (srcR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 0 256 (by omega) q hq))
  have notS : wires (notRegister (srcR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]; exact lsub w g _ (B 0 256 (by omega))
  have cmp : wires (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514))⊆(mSites w g).toFinset := by
    rw [(compareLt_wires none (srcR w) (xR w) (cR w) (w 513) (w 514) (by simp [srcR,xR,wireBlock_length])
      (by simp [cR,xR,wireBlock_length])).1]
    apply lsub; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 513 (by omega)
    · exact B 0 256 (by omega) q hq
    · exact B 770 256 (by omega) q hq
    · exact B 256 256 (by omega) q hq
  have hC : wires (comparePart w g k)⊆(mSites w g).toFinset := by
    simp only [comparePart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mskS _,notS⟩,cmp⟩,notS⟩,mskS _⟩
  have cx (a b : Nat) (ha : a < 515 ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have hP : wires (parGates w g k)⊆(mSites w g).toFinset := by
    unfold parGates
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hR' : wires (rotateRight (kR w))⊆(mSites w g).toFinset := by
    rw [(rotate_wires (kR w)).1]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub w g _ (B 770 258 (by omega))
  have hPr : wires (prodPart w g)⊆(mSites w g).toFinset := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub <;> intro q hq <;>
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hL : wires (loadK w g k)⊆(mSites w g).toFinset := by
    simp only [loadK,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub w g _ (B 0 258 (by omega)))
  have hK : wires (kAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hM1 : wires [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hM2 : wires [.measureX (w 721) [] [.CZ g (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl
    · exact I _ (by omega)
    · exact G
    · exact I _ (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mSites w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hH : wires (hAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · rw [dBits_wire w q hq]; exact I 1028 (by omega)
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mSites w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hT : wires (loadT w g k)⊆(mSites w g).toFinset := by
    simp only [loadT,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have hE : wires (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hHT : wires (hAddT w)⊆(mSites w g).toFinset := (hAddT_wires w).trans hH
  simp only [merged,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hC,hP,hR'⟩,hPr⟩,hL⟩,hK⟩,hL⟩,hM1⟩,hCp⟩,hHT⟩,hW⟩,hT⟩,hE⟩,hT⟩,hM2⟩


theorem merged_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (merged w g k)=1025 ∧ measurementCount (merged w g k)=1027 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := maskedConstant_counts c r v
  have x1 (r : List Wire) (v : Nat) := xorConstant_counts r v
  have n1 := notRegister_counts (srcR w)
  have c1' := compareLt_counts none (srcR w) (xR w) (cR w) (w 513) (w 514)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,xR,wireBlock_length])
  have r1 := rotate_counts (kR w)
  have k1 := mappedAdd_counts (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length])
  have h1 := mappedAdd_counts (dBits w) (hpR w) (hC2 w) (w 1797)
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length])
  have e1 := eraseLtChain_counts (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length])
  have cp1 := copyRegister_counts none (wireBlock w 770 257) (hpR w) (by simp [hpR,wireBlock_length])
  have pg : toffoliCount (parGates w g k)=0 ∧ measurementCount (parGates w g k)=0 := by
    unfold parGates; split_ifs <;> simp [toffoliCount,measurementCount]
  have lx : (xR w).length=256 := by simp [xR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  rw [lx] at c1'
  rw [lk] at k1
  rw [lh] at h1
  rw [lt] at e1
  have hT := hAddT_counts w
  rw [hAddM,h1.1,h1.2] at hT
  have hT' : toffoliCount (hAddT w)=255 ∧ measurementCount (hAddT w)=256 := by omega
  simp only [merged,comparePart,prodPart,loadK,kAddM,hT'.1,hT'.2,loadT,toffoliCount_append,
    measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,n1.1,n1.2,c1'.1,c1'.2.1,
    r1.1,r1.2.1,k1.1,k1.2,h1.1,h1.2,e1.1,e1.2,cp1.1,cp1.2,pg.1,pg.2]
  simp [toffoliCount,measurementCount]

section Phys
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_physical (k : Nat) : GatePhysical (merged w g k) := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j := w_ne w hn i j hi hj h
  have gn (i : Nat) (hi : i<1798) : g≠w i := g_ne w hn g hg i hi
  have cxp (a b : Wire) (h : a≠b) : GatePhysical [.CX a b] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h]
  have ccxp (a b c : Wire) (h1 : a≠c) (h2 : b≠c) : GatePhysical [.CCX a b c] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h1,h2]
  have mp (c : Wire) (c' : Wire) : GatePhysical [.measureX c [] [.CZ c' c]] ∧
      GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by
    simp [GatePhysical,PhysicalInstr]
  have gS : g∉srcR w := g_out w hn g hg 0 256 (by omega)
  have gH : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have cmpP : GatePhysical (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514)) := by
    apply compareLt_physical
    · have a1 := blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)
      have a2 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
      have a3 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
      have l1 : (srcR w++xR w).Nodup := List.nodup_append'.mpr ⟨src_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
      have l2 : (srcR w++xR w++cR w).Nodup := by
        apply List.nodup_append'.mpr
        refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
        apply List.disjoint_left.mpr
        intro q hq hc'
        rcases List.mem_append.mp hq with h1|h1
        · exact List.disjoint_left.mp a2 h1 hc'
        · exact List.disjoint_left.mp a3 h1 hc'
      simp only [List.cons_append,List.append_assoc] at l2 ⊢
      refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,by simpa [List.append_assoc] using l2⟩⟩
      · simp only [List.mem_cons,List.mem_append,not_or]
        exact ⟨ne 514 513 (by omega) (by omega) (by omega),nb w hn 514 0 256 (by omega) (by omega) (by omega),
          nb w hn 514 770 256 (by omega) (by omega) (by omega),nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
      · simp only [List.mem_append,not_or]
        exact ⟨nb w hn 513 0 256 (by omega) (by omega) (by omega),nb w hn 513 770 256 (by omega) (by omega) (by omega),
          nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
    · simp
  have kP : GatePhysical (kAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      refine ⟨?_,?_,?_⟩
      · intro e; exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq')
      · exact fun h' => hR_kR w hn _ h' hq'
      · exact fun h' => List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq' h'
  have hP : GatePhysical (hAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      have : q∈mappedWires (dBits w) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
      rw [dBits_wire w q this,List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne 1028 1797 (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
        nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have eP : GatePhysical (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)) := by
    apply eraseLtChain_physical
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    rw [List.cons_append,List.cons_append]
    refine List.nodup_cons.mpr ⟨?_,l2⟩
    simp only [List.mem_append,not_or]
    exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cpP : GatePhysical (copyRegister none (wireBlock w 770 257) (hpR w)) :=
    copyRegister_physical none _ _ (List.nodup_append'.mpr ⟨blk_nd w hn 770 257 (by omega),
      blk_nd w hn 1 257 (by omega),blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩) (by simp)
  have parP : GatePhysical (parGates w g k) := by
    unfold parGates
    split_ifs <;> simp only [gatePhysical_append] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first
        | exact cxp _ _ (ne _ _ (by omega) (by omega) (by omega))
        | exact cxp _ _ (gn _ (by omega))
        | simp [GatePhysical]
  have rotP := (rotate_physical (kR w) (kR_nd w hn)).1
  have prodP : GatePhysical (prodPart w g) := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,gatePhysical_append]
    exact ⟨ccxp _ _ _ (gn _ (by omega)) (ne _ _ (by omega) (by omega) (by omega)),
      ccxp _ _ _ (ne _ _ (by omega) (by omega) (by omega)) (ne _ _ (by omega) (by omega) (by omega))⟩
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h1286 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h1287 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t1286 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  have lkP : GatePhysical (loadK w g k) := by
    simp only [loadK,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨xorConstant_physical _ _,maskedConstant_physical _ _ _ gH⟩,maskedConstant_physical _ _ _ h514⟩,
      maskedConstant_physical _ _ _ h1028⟩,maskedConstant_physical _ _ _ h1286⟩,maskedConstant_physical _ _ _ h1287⟩
  have ltP : GatePhysical (loadT w g k) := by
    simp only [loadT,gatePhysical_append]
    exact ⟨maskedConstant_physical _ _ _ gT,maskedConstant_physical _ _ _ t1286⟩
  have w0P : GatePhysical [.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,ne 1028 0 (by omega) (by omega) (by omega)]
  have cP : GatePhysical (comparePart w g k) := by
    simp only [comparePart,gatePhysical_append]
    exact ⟨⟨⟨⟨maskedConstant_physical _ _ _ gS,notRegister_physical _⟩,cmpP⟩,notRegister_physical _⟩,
      maskedConstant_physical _ _ _ gS⟩
  have m1 : GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have m2 : GatePhysical [.measureX (w 721) [] [.CZ g (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have hPT : GatePhysical (hAddT w) := hAddT_physical w hP
  simp only [merged,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cP,parP,rotP⟩,prodP⟩,lkP⟩,kP⟩,lkP⟩,m1⟩,cpP⟩,hPT⟩,w0P⟩,ltP⟩,eP⟩,ltP⟩,m2⟩

end Phys

theorem gs1 (i : Instr) : Challenge.gateSlots [i]=Challenge.instructionSlots i := by
  simp [Challenge.gateSlots]

theorem merged_slots (w : Nat → Wire) (g : Wire) (k : Nat) : Challenge.gateSlots (merged w g k)≤25000 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := Baselines.maskedConstant_gateSlots_le c r v
  have x1 (r : List Wire) (v : Nat) := Baselines.xorConstant_gateSlots_le r v
  have c1' := Baselines.compareLt_gateSlots_le none (srcR w) (xR w) (cR w) (w 513) (w 514)
  have r1 := (Baselines.rotate_gateSlots_le (kR w)).1
  have k1 := Baselines.mappedAdd_gateSlots_le (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
  have h1 := Baselines.mappedAdd_gateSlots_le (dBits w) (hpR w) (hC2 w) (w 1797)
  have e1 := Baselines.eraseLt_gateSlots_le (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
  have pg : Challenge.gateSlots (parGates w g k)≤6 := by
    unfold parGates; split_ifs <;> simp [Challenge.gateSlots,Challenge.instructionSlots]
  have pr : Challenge.gateSlots (prodPart w g)=2 := by simp [prodPart,Challenge.gateSlots,Challenge.instructionSlots]
  have w0 : Challenge.gateSlots [.CX (w 1028) (w 0),.X (w 0)]=2 := by simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q1 : Challenge.gateSlots [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q2 : Challenge.gateSlots [.measureX (w 721) [] [.CZ g (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have lK : Challenge.gateSlots (loadK w g k)≤6*258 := by
    simp only [loadK,Challenge.gateSlots_append]
    have := x1 (hR w) (c1 k); have := m1 g (hR w) (cg k); have := m1 (w 514) (hR w) (cf k)
    have := m1 (w 1028) (hR w) (cp k); have := m1 (w 721) (hR w) (cgp k); have := m1 (w 722) (hR w) (cfp k)
    simp only [hR,wireBlock_length] at *
    omega
  have lT : Challenge.gateSlots (loadT w g k)≤2*256 := by
    simp only [loadT,Challenge.gateSlots_append]
    have := m1 g (tR w) (thrA k); have := m1 (w 721) (tR w) (thrB k)
    simp only [tR,wireBlock_length] at *
    omega
  have cP : Challenge.gateSlots (comparePart w g k)≤4*256+12*256+4 := by
    simp only [comparePart,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
    have := m1 g (srcR w) (cmpC+k)
    simp only [srcR,xR,wireBlock_length] at *
    omega
  have cp : Challenge.gateSlots (copyRegister none (wireBlock w 770 257) (hpR w))=257 := by
    simp [hpR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hp8 w).length=256 := by simp [hp8,wireBlock_length]
  have lhR : (hR w).length=258 := by simp [hR,wireBlock_length]
  rw [lk] at r1
  rw [mappedRead_length,lhR] at k1
  rw [dBits_length] at h1
  rw [lh] at e1
  have hS := hAddT_slots w
  rw [hAddM] at hS
  simp only [merged,Challenge.gateSlots_append,pr,w0,q1,q2,cp,kAddM]
  omega

end ECDSAAdd.Entrant.E1Merge

end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.E1QubitPlacement =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Prefix1590Point
-- consolidated import: import ECDSAAdd.Submission.Entrant.FrontierEntry1591Native
-- consolidated import: import ECDSAAdd.Submission.Entrant.E1Merge

/-! Research source. Complete proof bodies, adapted from the pinned accepted
E1 placement proof to a different bijection. No sorry/axiom/certificate.
Not elaborated or replayed in this environment. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1QubitPlacement
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk

/-! Complete zero-cost placement for E1 on the old Q1588 rolling route.
The global bijection first moves three E1-only scratch locations:
  compare carry511 ->725, product721 ->723, product722 ->724.
It then hosts native cin1797 at511 and applies the three rolling phase hosts.
No two live values are aliased. All added destinations are already-counted
ordinary field carry sites. This file has NOT been Lean-checked here. -/

def nativeSwap : Equiv.Perm Wire := Equiv.swap (base 1797) (base 511)
def phaseHost : Equiv.Perm Wire :=
  (Equiv.swap (base 1026) (base 721)).trans
    ((Equiv.swap (base 1541) (base 722)).trans
      (Equiv.swap (base 1542) (base 720)))
def sig (q : Wire) : Wire := phaseHost (nativeSwap q)
def pmap (L : ControlledPointLayout) (q : Wire) : Wire := wireFn2 L (sig q)

def sw (i : Nat) : Nat :=
  if i=1797 then 511 else if i=511 then 1797 else
  if i=1026 then 721 else if i=721 then 1026 else
  if i=1541 then 722 else if i=722 then 1541 else
  if i=1542 then 720 else if i=720 then 1542 else i

theorem swap_base (a b i : Nat) :
    Equiv.swap (base a) (base b) (base i)=base (if i=a then b else if i=b then a else i) := by
  rw [Equiv.swap_apply_def]
  by_cases h1 : i=a
  · subst h1; simp
  · have n1 : base i≠base a := fun e => h1 (base_injective e)
    by_cases h2 : i=b
    · subst h2; simp [n1,h1]
    · have n2 : base i≠base b := fun e => h2 (base_injective e)
      simp [n1,n2,h1,h2]

theorem sig_base (i : Nat) : sig (base i)=base (sw i) := by
  unfold sig phaseHost nativeSwap
  simp only [Equiv.trans_apply,swap_base]
  congr 1
  unfold sw
  split_ifs <;> omega

theorem sig_injective : Function.Injective sig :=
  phaseHost.injective.comp nativeSwap.injective

/-- The label set of the merged circuit. -/
def S : Finset Wire := (E1Merge.mSites base (base 2400)).toFinset

theorem S_cases (q : Wire) (hq : q∈S) : ∃ i, q=base i ∧
    (i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722 ∨ i = 2400) := by
  simp only [S,E1Merge.mSites,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false] at hq
  rcases hq with ((h|h)|h)|h|h|h
  all_goals first
    | (obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
       simp only [List.mem_range'_1] at hi
       exact ⟨i,rfl,by omega⟩)
    | exact ⟨_,h,by omega⟩

/-- Label range of the merged circuit after the scratch relocation `rho`. -/
abbrev Rng (i : Nat) : Prop :=
  (i < 515 ∧ i ≠ 511) ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 723 ∨ i = 724 ∨ i = 725 ∨ i = 2400

theorem sw_slot (i : Nat) (hi : Rng i) : base (sw i)∈slots.toFinset := by
  apply slot_mem
  · unfold live sw; split_ifs <;> omega
  · unfold CompressedAllocation.omitted sw; split_ifs <;> omega

theorem sw_logical (i : Nat) (hi : Rng i) : base (sw i)∈OB5Support.logicalSites := by
  simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
  refine ⟨sw i,?_,rfl⟩
  simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
  unfold sw; split_ifs <;> omega

/-- Three disjoint E1 scratch relocations. The direct tick omits all six ports. -/
def rho : Equiv.Perm Wire :=
  (Equiv.swap (base 511) (base 725)).trans
    ((Equiv.swap (base 721) (base 723)).trans (Equiv.swap (base 722) (base 724)))
def rhoN (i : Nat) : Nat :=
  if i=511 then 725 else if i=725 then 511 else
  if i=721 then 723 else if i=723 then 721 else
  if i=722 then 724 else if i=724 then 722 else i

theorem rho_base (i : Nat) : rho (base i)=base (rhoN i) := by
  unfold rho rhoN
  simp only [Equiv.trans_apply,swap_base]
  congr 1
  split_ifs <;> omega

theorem rho_injective : Function.Injective rho := rho.injective

theorem rhoN_range (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722 ∨ i = 2400) :
    Rng (rhoN i) := by
  unfold Rng rhoN; split_ifs <;> omega

/-- Placement of the merged circuit: relocation, the four relabelings, the layout map. -/
def pmapR (L : ControlledPointLayout) (q : Wire) : Wire := pmap L (rho q)


theorem sig_rho_x (i : Nat) (hi : 770≤ i ∧ i<1026) :
    sig (rho (base i))=base i := by
  have hr : rhoN i=i := by unfold rhoN;split_ifs <;> omega
  have hs : sw i=i := by unfold sw;split_ifs <;> omega
  rw [rho_base,hr,sig_base,hs]

section Place
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem pmap_inj : ∀a∈S,∀b∈S,pmapR L a=pmapR L b → a=b := by
  intro a ha b hb e
  obtain ⟨i,rfl,hi⟩ := S_cases a ha
  obtain ⟨j,rfl,hj⟩ := S_cases b hb
  have pl := placement2 L hw hn
  unfold pmapR pmap at e
  rw [rho_base,rho_base,sig_base,sig_base] at e
  have := pl.injectiveOnSlots _ (sw_slot _ (rhoN_range i hi)) _ (sw_slot _ (rhoN_range j hj)) e
  rw [←sig_base,←sig_base] at this
  have := sig_injective this
  rw [←rho_base,←rho_base] at this
  exact rho_injective this

theorem pmap_x : (wireBlock base 770 256).map (pmapR L)=L.point.x := by
  have pl := placement2 L hw hn
  rw [←pl.divisorMap]
  apply List.map_congr_left
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  change wireFn2 L (sig (rho (base i)))=wireFn2 L (base i)
  rw [sig_rho_x i (by omega)]

theorem pmap_g : pmapR L (base 2400)=L.core.generic := by
  have pl := placement2 L hw hn
  unfold pmapR pmap; rw [rho_base,sig_base]
  have : sw (rhoN 2400)=2400 := by unfold sw rhoN; simp
  rw [this]; exact pl.controlMap

theorem pmap_pool (q : Wire) (hq : q∈S) (hx : q∉wireBlock base 770 256) (hg : q≠base 2400) :
    pmapR L q∈L.dialogPool := by
  obtain ⟨i,rfl,hi⟩ := S_cases q hq
  have pl := placement2 L hw hn
  let j:=sw (rhoN i)
  have indexEq : sig (rho (base i))=base j := by rw [rho_base,sig_base]
  have injective:=sig_injective.comp rho_injective
  have fixedG : sig (rho (base 2400))=base 2400 := by decide +kernel
  have jRange : j<1798 ∨ j=2400 := by
    have range:=rhoN_range i hi
    dsimp [j]
    generalize rhoN i=v at range ⊢
    unfold Rng at range
    unfold sw
    split_ifs <;> omega
  have jNotG : j≠2400 := by
    intro e
    apply hg
    exact injective (indexEq.trans ((congrArg base e).trans fixedG.symm))
  have jlt : j<1798 := by omega
  have jNotX : ¬(770≤ j ∧ j<1026) := by
    intro bounds
    have equal:=injective (indexEq.trans (sig_rho_x j bounds).symm)
    have same:=base_injective equal
    apply hx
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1];omega,rfl⟩
  change wireFn2 L (sig (rho (base i)))∈L.dialogPool
  rw [indexEq]
  apply pl.sharedWork
  · exact List.mem_map.mpr ⟨j,by simp only [skywalkSharedWires,List.mem_range'_1];omega,rfl⟩
  · exact sw_slot _ (rhoN_range i hi)
  · intro h
    obtain ⟨v,hv,e⟩:=List.mem_map.mp h
    have same:=base_injective e
    simp only [List.mem_range'_1] at hv
    exact jNotX (by omega)
  · intro h
    obtain ⟨v,hv,e⟩:=List.mem_map.mp h
    have same:=base_injective e
    simp only [List.mem_range'_1] at hv
    omega

end Place


def tickF (L : ControlledPointLayout) : Program := renameProgram (pmapR L) (NativeFirstDirect.forward base)
def entryM (L : ControlledPointLayout) (k : Fp) : Program :=
  renameProgram (pmapR L) (E1Merge.merged base (base 2400) k.val)

theorem regValue_pull (f : Wire → Wire) (r : List Wire) (s : BasisState) :
    regValue r (fun q => s (f q))=regValue (r.map f) s := by
  induction r with
  | nil => rfl
  | cons a rs ih =>
    change (if s (f a) then 1 else 0)+2*regValue rs (fun q => s (f q))=
      (if s (f a) then 1 else 0)+2*regValue (rs.map f) s
    rw [ih]

theorem g2400 : base 2400∉skywalkPoolWires base := by
  intro h
  obtain ⟨i,hi,e⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hi
  have := base_injective e; omega

theorem merged_S (k : Nat) : wires (E1Merge.merged base (base 2400) k)⊆S :=
  E1Merge.merged_support base (base 2400) k

theorem prefix_S : (NativeFirstDirect.prefixSites base).toFinset⊆S := by
  intro q h
  rw [List.mem_toFinset] at h
  simp only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at h
  simp only [S,List.mem_toFinset]
  rcases h with ((h|h)|h)|h|h
  · exact E1Merge.blk_mSites base (base 2400) 0 257 (by omega) q h
  · exact E1Merge.blk_mSites base (base 2400) 770 258 (by omega) q h
  · exact E1Merge.blk_mSites base (base 2400) 1540 256 (by omega) q h
  · rw [h]; exact E1Merge.in_mSites base (base 2400) 1028 (by omega)
  · rw [h]; exact E1Merge.in_mSites base (base 2400) 1797 (by omega)

theorem forward_S : wires (NativeFirstDirect.forward base)⊆S :=
  Finset.Subset.trans (NativeFirstDirect.prefix_support base).1 prefix_S

section Entry
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

/-- Physical form: the merged entry equals the compare-first constant addition followed by the
renamed direct first tick, on every pair of measurement records. -/
theorem entry_eq (k : Fp) (s : State) (X : Nat) (hX : X<p) (G : Bool)
    (hx : regValue L.point.x s.basis=X) (hg : s.basis L.core.generic=G)
    (hc : regValue L.dialogPool s.basis=0) (m1 m2 : List Bool) :
    run (entryM L k) m1 s=run (fastConstAdd L L.point.x k++tickF L) m2 s := by
  have inj := pmap_inj L hw hn
  have pool := pmap_pool L hw hn
  have hzero := (regValue_zero _ _).mp hc
  let F := pmapR L
  let t : State := pullState F s
  have clean (q : Wire) (hq : q∈S) (h1 : q∉wireBlock base 770 256) (h2 : q≠base 2400) :
      t.basis q=false := hzero _ (pool q hq h1 h2)
  have inS (i : Nat) (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      base i∈S := List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i hi)
  have notx (i : Nat) (hi : ¬ (770 ≤ i ∧ i < 1026)) : base i∉wireBlock base 770 256 := by
    intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj; have := base_injective e; omega
  have ne2400 (i : Nat) (hi : i≠2400) : base i≠base 2400 := fun e => hi (base_injective e)
  have cl (i : Nat) (hi : i < 515 ∨ (1026 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      t.basis (base i)=false :=
    clean _ (inS i (by omega)) (notx i (by omega)) (ne2400 i (by omega))
  have blkz (a n : Nat) (h : a + n ≤ 515 ∨ (1026 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
      regValue (wireBlock base a n) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (by omega)
  have xval : regValue (wireBlock base 770 256) t.basis=X := by
    change regValue (wireBlock base 770 256) (fun q => s.basis (F q))=X
    rw [regValue_pull,pmap_x L hw hn,hx]
  have tk0 : regValue (E1Merge.kR base) t.basis=X := by
    rw [E1Merge.kR_x base base_pool_nodup,show E1Merge.xR base=wireBlock base 770 256 from rfl,xval,
      blkz 1026 2 (by omega)]
    simp
  have tg : t.basis (base 2400)=G := by
    change s.basis (pmapR L (base 2400))=G
    rw [pmap_g L hw hn,hg]
  -- old side
  have fca := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX s
    (m2.take (measurementCount (fastConstAdd L L.point.x k))) hg hx hc
  generalize hs1 : run (fastConstAdd L L.point.x k) (m2.take (measurementCount (fastConstAdd L L.point.x k))) s=s1 at fca
  obtain ⟨p1,x1,o1⟩ := fca
  let u : State := ⟨t.phase,fun q => if q∈E1Merge.kR base then s1.basis (F q) else t.basis q⟩
  have hu2 : ∀q,q∉E1Merge.kR base → u.basis q=t.basis q := by
    intro q hq; simp [u,hq]
  have xS : ∀q∈L.point.x,∃a∈S,F a=q ∧ a∈wireBlock base 770 256 := by
    intro q hq
    rw [←pmap_x L hw hn] at hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    refine ⟨a,?_,rfl,ha⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_range'_1] at hi
    exact inS i (by omega)
  have hu3 : regValue (E1Merge.kR base) u.basis=(X+(if t.basis (base 2400) then k.val else 0))%p := by
    rw [tg,E1Merge.kR_x base base_pool_nodup]
    have e1 : regValue (E1Merge.xR base) u.basis=regValue L.point.x s1.basis := by
      rw [←pmap_x L hw hn,←regValue_pull]
      apply regValue_congr
      intro q hq
      have : q∈E1Merge.kR base := E1Merge.blk_sub base 770 256 770 258 (by omega) (by omega) q hq
      simp only [u,this,if_true]
      rfl
    have e2 : regValue (wireBlock base 1026 2) u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      have kq : base i∈E1Merge.kR base := E1Merge.blk_sub base 1026 2 770 258 (by omega) (by omega) _ hq
      have outx : F (base i)∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha (base i) (inS i (by omega)) ea
        subst this
        exact notx i (by omega) ax
      simp only [u,kq,if_true]
      rw [o1 _ outx]
      exact cl i (by omega)
    rw [e1,e2,x1]; simp
  have t1 := (regValue_zero _ _).mp (blkz 0 258 (by omega))
  have eqL := E1Merge.merged_eq_forward base (base 2400) base_pool_nodup g2400 k.val k.isLt X hX t u m1
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) tk0 (blkz 0 258 (by omega))
    (blkz 1029 256 (by omega)) (cl 1028 (by omega)) (cl 514 (by omega)) (cl 721 (by omega)) (cl 722 (by omega))
    (fun i h1 h2 => cl i (by omega)) (cl 513 (by omega))
    (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact cl i (by omega)) (cl 1797 (by omega)) rfl hu2 hu3
  -- transport both sides
  have hS : ∀q∈S,t.basis q=s.basis (F q) := fun q _ => rfl
  have newSide := run_rename_pool F S inj _ (merged_S k.val) m1 t s rfl hS
  have uS : ∀q∈S,u.basis q=s1.basis (F q) := by
    intro q hq
    by_cases kq : q∈E1Merge.kR base
    · simp [u,kq]
    · simp only [u,kq,if_false]
      change s.basis (F q)=s1.basis (F q)
      have outx : F q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha q hq ea
        subst this
        exact kq (E1Merge.blk_sub base 770 256 770 258 (by omega) (by omega) _ ax)
      rw [o1 _ outx]
  have oldSide := run_rename_pool F S inj _ forward_S
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) u s1 (by simp [u,t,pullState,p1]) uS
  have rhs : run (fastConstAdd L L.point.x k++tickF L) m2 s=
      run (tickF L) (m2.drop (measurementCount (fastConstAdd L L.point.x k))) s1 := by
    rw [run_append,hs1]
  rw [rhs]
  apply State.extensionality
  · rw [entryM,newSide.1,eqL,tickF,oldSide.1]
  · funext q
    by_cases im : q∈S.image F
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp im
      rw [entryM,newSide.2 a ha,eqL,tickF,oldSide.2 a ha]
    · rw [entryM,run_rename_pool_outside F S _ (merged_S k.val) m1 s q im,tickF,
        run_rename_pool_outside F S _ forward_S _ s1 q im]
      have outx : q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,_⟩ := xS _ hm
        exact im (Finset.mem_image.mpr ⟨a,ha,ea⟩)
      rw [o1 q outx]

end Entry

/-- Replace a prefix whose final state agrees with an old prefix on every record. -/
theorem tri_transfer {P Q : BasisState → Prop} {A B R : Program}
    (h : ∀s : State,P s.basis → ∀ m1 m2 : List Bool,run A m1 s=run B m2 s)
    (t : Triple P (B++R) Q) : Triple P (A++R) Q := by
  intro s m hs
  have := t s (List.replicate (measurementCount B) false++m.drop (measurementCount A)) hs
  rw [run_append] at this ⊢
  have e1 : (List.replicate (measurementCount B) false++m.drop (measurementCount A)).take
      (measurementCount B)=List.replicate (measurementCount B) false := by simp
  have e2 : (List.replicate (measurementCount B) false++m.drop (measurementCount A)).drop
      (measurementCount B)=m.drop (measurementCount A) := by simp
  rw [e1,e2] at this
  rw [h s hs (m.take (measurementCount A)) (List.replicate (measurementCount B) false)]
  exact this

section Entry1
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

-- Keep the inherited width argument for existing callers.
set_option linter.unusedSectionVars false in
theorem lay (q : Wire) :
    (q∈L.point.x → q∉L.point.y) ∧ (q∈L.dialogPool → q∉L.point.x ∧ q∉L.point.y) ∧
    (q=L.core.generic → q∉L.point.x ∧ q∉L.point.y) := by
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  refine ⟨fun hx hy => ?_,fun hp => ⟨fun hx => ?_,fun hy => ?_⟩,fun hg => ⟨fun hx => ?_,fun hy => ?_⟩⟩
  all_goals
    first
    | (have h1 := List.count_pos_iff.mpr hx; have h2 := List.count_pos_iff.mpr hy
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil] at h
       omega)
    | (have h1 := List.count_pos_iff.mpr hp; have h2 := List.count_pos_iff.mpr hx
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil] at h
       omega)
    | (have h1 := List.count_pos_iff.mpr hp; have h2 := List.count_pos_iff.mpr hy
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil] at h
       omega)
    | (subst hg; have h2 := List.count_pos_iff.mpr hx
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
       omega)
    | (subst hg; have h2 := List.count_pos_iff.mpr hy
       simp only [dialogUsedWires,inPlaceFlags,PointAddLayout.pointWires,
         List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
       omega)

/-- The y-side fused offset commutes with the x-side constant addition, so the merged x entry
can run after it. -/
theorem entry1_eq (k ky : Fp) (s : State) (X : Nat) (hX : X<p) (Y : Fp) (G : Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (hg : s.basis L.core.generic=G) (hc : regValue L.dialogPool s.basis=0) (m1 m2 : List Bool) :
    run (EntryFuse.fusedY L ky++entryM L k) m1 s=
      run (fastConstAdd L L.point.x k++EntryFuse.fusedY L ky++tickF L) m2 s := by
  have xy (q : Wire) (h : q∈L.point.x) : q∉L.point.y := (lay L hw hn q).1 h
  have px (q : Wire) (h : q∈L.dialogPool) : q∉L.point.x := ((lay L hw hn q).2.1 h).1
  have py (q : Wire) (h : q∈L.dialogPool) : q∉L.point.y := ((lay L hw hn q).2.1 h).2
  have gx : L.core.generic∉L.point.x := ((lay L hw hn _).2.2 rfl).1
  have gy : L.core.generic∉L.point.y := ((lay L hw hn _).2.2 rfl).2
  -- left: fusedY then merged entry
  have fy := EntryFuse.fusedY_correct L hw hn Y ky s (m1.take (measurementCount (EntryFuse.fusedY L ky))) hy hc
  generalize hsy : run (EntryFuse.fusedY L ky) (m1.take (measurementCount (EntryFuse.fusedY L ky))) s=sy at fy
  obtain ⟨py1,py2,py3⟩ := fy
  have syx : regValue L.point.x sy.basis=X := by
    rw [regValue_congr _ _ s.basis (fun q hq => py3 q (xy q hq)),hx]
  have syg : sy.basis L.core.generic=G := (py3 _ gy).trans hg
  have syc : regValue L.dialogPool sy.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq => py3 q (py q hq)),hc]
  -- commutation of the two constant steps
  have comm (r0 r1 r2 : List Bool) : run (fastConstAdd L L.point.x k) r0 sy=
      run (EntryFuse.fusedY L ky) r2 (run (fastConstAdd L L.point.x k) r1 s) := by
    have fa := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX sy r0 syg syx syc
    have fc := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k X G hX s r1 hg hx hc
    generalize ha : run (fastConstAdd L L.point.x k) r0 sy=a at fa
    generalize hcc : run (fastConstAdd L L.point.x k) r1 s=c at fc
    obtain ⟨a1,a2,a3⟩ := fa
    obtain ⟨c1,c2,c3⟩ := fc
    have cy : regValue L.point.y c.basis=Y.val := by
      rw [regValue_congr _ _ s.basis (fun q hq => c3 q (fun h => xy q h hq)),hy]
    have cc : regValue L.dialogPool c.basis=0 := by
      rw [regValue_congr _ _ s.basis (fun q hq => c3 q (px q hq)),hc]
    have fb := EntryFuse.fusedY_correct L hw hn Y ky c r2 cy cc
    generalize hb : run (EntryFuse.fusedY L ky) r2 c=b at fb
    obtain ⟨b1,b2,b3⟩ := fb
    have cg : c.basis L.core.generic=s.basis L.core.generic := c3 _ gx
    apply State.extensionality
    · rw [a1,b1,c1,py1]
    · funext q
      by_cases qx : q∈L.point.x
      · have e : regValue L.point.x a.basis=regValue L.point.x b.basis := by
          rw [a2,regValue_congr _ _ c.basis (fun q hq => b3 q (xy q hq)),c2]
        exact (regValue_eq_iff _ _ _).mp e q qx
      by_cases qy : q∈L.point.y
      · have e : regValue L.point.y a.basis=regValue L.point.y b.basis := by
          rw [regValue_congr _ _ sy.basis (fun q hq => a3 q (fun h => xy q h hq)),py2,b2,cg]
        exact (regValue_eq_iff _ _ _).mp e q qy
      rw [a3 q qx,b3 q qy,c3 q qx,py3 q qy]
  -- assemble
  let nA := measurementCount (fastConstAdd L L.point.x k)
  let nY := measurementCount (EntryFuse.fusedY L ky)
  let M := List.replicate nA false++m2.drop (nA+nY)
  have lhs : run (EntryFuse.fusedY L ky++entryM L k) m1 s=
      run (tickF L) (m2.drop (nA+nY)) (run (fastConstAdd L L.point.x k) (List.replicate nA false) sy) := by
    rw [run_append,hsy,entry_eq L hw hn k sy X hX G syx syg syc _ M,run_append]
    have t1 : M.take nA=List.replicate nA false := List.take_left' (by simp)
    have t2 : M.drop nA=m2.drop (nA+nY) := List.drop_left' (by simp)
    rw [t1,t2]
  have rhs : run (fastConstAdd L L.point.x k++EntryFuse.fusedY L ky++tickF L) m2 s=
      run (tickF L) (m2.drop (nA+nY)) (run (EntryFuse.fusedY L ky) ((m2.take (nA+nY)).drop nA)
        (run (fastConstAdd L L.point.x k) ((m2.take (nA+nY)).take nA) s)) := by
    rw [run_append,run_append,measurementCount_append]
  rw [lhs,rhs,comm]

end Entry1

/-! Resource and support facts are independent of the point-level caller. -/
section Resources
open Challenge
attribute [local irreducible] wires

def logicalEntry (k : Nat) : Program :=
  renameProgram sig (renameProgram rho (E1Merge.merged base (base 2400) k))

theorem entryM_eq (L : ControlledPointLayout) (k : Fp) :
    entryM L k=renameProgram (wireFn2 L) (logicalEntry k.val) := by
  simp only [entryM,logicalEntry,renameProgram_comp]
  rfl

private theorem renamed_twice_labels (f h : Wire→Wire) (P : Program) (U : Finset Wire)
    (sub : wires P⊆U) (q : Wire) (hq : q∈wires (renameProgram f (renameProgram h P))) :
    ∃b∈U,q=f (h b) := by
  rw [renameProgram_support,renameProgram_support] at hq
  obtain ⟨a,ha,ea⟩:=Finset.mem_image.mp hq
  obtain ⟨b,hb,eb⟩:=Finset.mem_image.mp ha
  refine ⟨b,sub hb,?_⟩
  rw [←ea,←eb]


theorem merged_labels (k : Nat) (q : Wire) (hq : q∈wires (logicalEntry k)) :
    ∃ j, q=base (sw (rhoN j)) ∧
      (j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨
        j=721 ∨ j=722 ∨ j=2400) := by
  obtain ⟨b,hb,eq⟩:=renamed_twice_labels sig rho
    (E1Merge.merged base (base 2400) k) S (merged_S k) q hq
  obtain ⟨j,rfl,hj⟩:=S_cases b hb
  refine ⟨j,?_,hj⟩
  rw [eq,rho_base,sig_base]

theorem logicalM (k : Nat) : wires (logicalEntry k)⊆OB5Support.logicalSites := by
  intro q hq
  obtain ⟨j,rfl,hj⟩ := merged_labels k q hq
  exact sw_logical _ (rhoN_range j hj)

theorem sw_avoid (j : Nat)
    (hj : j < 515 ∨ (770 ≤ j ∧ j < 1285) ∨ (1540 ≤ j ∧ j < 1798) ∨
      j=721 ∨ j=722 ∨ j=2400) :
    sw (rhoN j)∉[2312,766,765,767,1026,1541,1542,1797,768,718,719] := by
  have range:=rhoN_range j hj
  generalize rhoN j=i at range ⊢
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  unfold Rng at range
  unfold sw
  split_ifs <;> omega

theorem merged_omits (k i : Nat)
    (hi : i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719]) :
    base i∉wires (logicalEntry k) := by
  intro h
  obtain ⟨j,e,hj⟩ := merged_labels k (base i) h
  have eq := base_injective e
  exact sw_avoid j hj (eq ▸ hi)

theorem entryM_counts (L : ControlledPointLayout) (k : Fp) :
    toffoliCount (entryM L k)=1025 ∧ measurementCount (entryM L k)=1027 := by
  have r := renameProgram_counts (pmapR L) (E1Merge.merged base (base 2400) k.val)
  have c := E1Merge.merged_counts base (base 2400) k.val
  rw [entryM,r.1,r.2]; exact c

theorem tickF_counts (L : ControlledPointLayout) :
    toffoliCount (tickF L)=508 ∧ measurementCount (tickF L)=508 := by
  have r := renameProgram_counts (pmapR L) (NativeFirstDirect.forward base)
  have c := NativeFirstDirect.forward_counts base
  rw [tickF,r.1,r.2]; exact c

theorem entryM_slots (L : ControlledPointLayout) (k : Fp) :
    gateSlots (entryM L k)≤25000 := by
  simpa only [entryM,Baselines.rename_gateSlots] using
    E1Merge.merged_slots base (base 2400) k.val

theorem entryM_sites (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryM L k)⊆(OB5Support.sites L).toFinset := by
  rw [entryM_eq]
  exact OB5Support.placed_support_logical L hw _ (logicalM k.val)

theorem entryM_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (entryM L k) := by
  rw [entryM]
  exact gatePhysical_rename_support (pmapR L) (E1Merge.merged base (base 2400) k.val)
    (fun a ha b hb e => pmap_inj L hw hn a (merged_S k.val ha) b (merged_S k.val hb) e)
    (E1Merge.merged_physical base (base 2400) base_pool_nodup g2400 k.val)

theorem prefix_counts (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    toffoliCount (entryM L k)+249=
      toffoliCount (fastConstAdd L L.point.x k++tickF L) ∧
    measurementCount (entryM L k)+248=
      measurementCount (fastConstAdd L L.point.x k++tickF L) := by
  have a := fastConstAdd_counts L hw L.point.x (Or.inl rfl) k
  have e := entryM_counts L k
  have t := tickF_counts L
  simp only [toffoliCount_append,measurementCount_append]
  constructor <;> omega

end Resources

/-- All pre-relocated ports are absent from the actual direct first tick. -/
theorem rho_fix (f : Wire → Wire) :
    renameProgram (fun q => f (rho q)) (NativeFirstDirect.forward base)=
      renameProgram f (NativeFirstDirect.forward base) := by
  have fix (P : Program) (support : wires P⊆(NativeFirstDirect.prefixSites base).toFinset) :
      renameProgram (fun q => f (rho q)) P=renameProgram f P := by
    apply renameProgram_congr_support
    intro q hq
    have h := support hq
    rw [List.mem_toFinset] at h
    simp only [NativeFirstDirect.prefixSites,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at h
    have e : ∃ i, q=base i ∧
        (i<257 ∨ (770≤ i ∧ i<1028) ∨ (1540≤ i ∧ i<1796) ∨ i=1028 ∨ i=1797) := by
      rcases h with ((h|h)|h)|h|h
      all_goals first
        | (obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
           simp only [List.mem_range'_1] at hi
           exact ⟨i,rfl,by omega⟩)
        | exact ⟨_,h,by omega⟩
    obtain ⟨i,rfl,hi⟩ := e
    rw [rho_base]
    have fixed : rhoN i=i := by unfold rhoN; split_ifs <;> omega
    rw [fixed]
  exact fix (NativeFirstDirect.forward base) (NativeFirstDirect.prefix_support base).1

/-- The new merged entry has exactly the old rolling native tick boundary. -/
theorem tick_eq (L : ControlledPointLayout) :
    renameProgram (wireFn2 L)
      (renameProgram phaseHost (FrontierEntry1591Native.forward base))=tickF L := by
  rw [tickF,show pmapR L=fun q => pmap L (rho q) from rfl,rho_fix]
  simp only [FrontierEntry1591Native.forward,FrontierEntry1591Native.Transport.program,
    renameProgram_comp]
  rfl

end ECDSAAdd.Entrant.E1QubitPlacement
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.E1Reflected =====
section
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectForwardProof
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectValues
-- consolidated import: import ECDSAAdd.Arithmetic.Compare
-- consolidated import: import ECDSAAdd.Arithmetic.ComparePhysical
-- consolidated import: import ECDSAAdd.Arithmetic.MaskedConstant
-- consolidated import: import ECDSAAdd.Arithmetic.MappedSources
-- consolidated import: import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.Copy
-- consolidated import: import ECDSAAdd.Arithmetic.Rotate
-- consolidated import: import ECDSAAdd.Arithmetic.Reduction
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredGateSupport
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectSupport
-- consolidated import: import ECDSAAdd.Baselines.SlotAlgebra
-- consolidated import: import ECDSAAdd.Baselines.SlotMapped
-- consolidated import: import ECDSAAdd.Baselines.SlotNativeFirst

set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Research adaptation of pinned accepted E1Merge. Reflects canonical input
unconditionally, then performs its controlled constant addition and first tick.
Full proof bodies are supplied; this module has NOT been Lean-checked here.
Input/output contract remains full State and every measurement record. -/
namespace ECDSAAdd.Entrant.E1Reflected
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum

/-! ### Arithmetic of the merged first tick -/

theorem p_val : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  norm_num [ECDSAAdd.p]

/-- bit 0 of the selected constant `g·k − f·p`. -/
def ksel0 (k : Nat) (G f : Bool) : Bool := (G && decide (k%2=1)) ^^ f
/-- low bit of the input implied by `(g,f,par)`. -/
def x0 (k : Nat) (G f par : Bool) : Bool := par ^^ ksel0 k G f

/-- Constant added to the complemented 258-bit `x>>1` bank to obtain the direct first-tick `K` word. -/
def tk (k : Nat) (G f par : Bool) : Nat :=
  if f then
    if G then (kConstant false par+1+(k-1-(x0 k G f par).toNat-par.toNat)/2)%2^258
    else 0
  else (kConstant false par+1+
    (p-1-(x0 k G f par).toNat+(if G then k else 0)-par.toNat)/2)%2^258

def delta (par : Bool) : Nat := if par then p else 2^257-p

def thr (k : Nat) (G par : Bool) : Nat := if G then (if par then (k+p+1)/2 else (k+1)/2) else 0

theorem hC_val : hConstant = 57896044618658097711785492504343953926634992332820282019728792003954417335832 := by
  norm_num [hConstant, ECDSAAdd.p]
theorem kC_val (par : Bool) : kConstant false par =
    if par then 405272312330606683982498447530407677486444946329741974138101544027698101223913
    else 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  cases par <;> norm_num [kConstant, ECDSAAdd.p]


theorem arith (k X : Nat) (hk : k<p) (hX : X<p) (G : Bool) :
    let f := decide (X<(if G then k else 0))
    let dx := (p-1-X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    decide (X%2=1)=x0 k G f par ∧
    (2^258-1-X/2+tk k G f par)%2^258=K ∧
    H=dx/2+(if par then hConstant else 0) ∧
    f=decide (H<thr k G par) ∧
    tk k G f par<2^258 := by
  intro f dx par K H
  rw [p_val] at hk hX
  simp only [f,dx,par,K,H,tk,delta,thr,x0,ksel0,kC_val,hC_val,p_val,Nat.reducePow]
  clear H K par dx f
  cases G
  · have e1 : (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+0)%115792089237316195423570985008687907853269984665640564039457584007908834671663=115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X :=
      Nat.mod_eq_of_lt (by omega)
    simp only [if_false,Bool.false_eq_true,Nat.not_lt_zero,decide_false,
      e1,Bool.false_and,Bool.false_xor,Bool.xor_false]
    rcases Nat.mod_two_eq_zero_or_one (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X) with h|h <;>
      simp only [h,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),
        by (first | exact True.intro | omega),by (first | exact True.intro | omega),
        by (first | exact True.intro | (rw [eq_comm,decide_eq_true_iff]; omega) |
          (rw [eq_comm,decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
  · simp only [if_true,Bool.true_and]
    by_cases hf : X<k
    · have e1 : (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=k-1-X := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
        omega
      have e2 : decide (X<k)=true := by simp [hf]
      simp only [e1,e2,Bool.xor_true]
      rcases Nat.mod_two_eq_zero_or_one (k-1-X) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),
        by (first | exact True.intro | omega),by (first | exact True.intro | omega),
        by (first | exact True.intro | (rw [eq_comm,decide_eq_true_iff]; omega) |
          (rw [eq_comm,decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
    · have e1 : (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+k := Nat.mod_eq_of_lt (by omega)
      have e2 : decide (X<k)=false := by simp [hf]
      simp only [e1,e2,Bool.xor_false]
      rcases Nat.mod_two_eq_zero_or_one (115792089237316195423570985008687907853269984665640564039457584007908834671663-1-X+k) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),
        by (first | exact True.intro | omega),by (first | exact True.intro | omega),
        by (first | exact True.intro | (rw [eq_comm,decide_eq_true_iff]; omega) |
          (rw [eq_comm,decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩

/-! ### Circuit -/

def cmpC : Nat := 2^256-p

def srcR (w : Nat → Wire) : List Wire := wireBlock w 0 256
def xR (w : Nat → Wire) : List Wire := wireBlock w 770 256
def cR (w : Nat → Wire) : List Wire := wireBlock w 256 256
def hR (w : Nat → Wire) : List Wire := wireBlock w 0 258
def kR (w : Nat → Wire) : List Wire := wireBlock w 770 258
def tR (w : Nat → Wire) : List Wire := wireBlock w 1029 256
def hpR (w : Nat → Wire) : List Wire := wireBlock w 1 257
def aC (w : Nat → Wire) : List Wire := wireBlock w 1540 257
def hC2 (w : Nat → Wire) : List Wire := wireBlock w 1540 256
def hp8 (w : Nat → Wire) : List Wire := wireBlock w 1 256
def hC3 (w : Nat → Wire) : List Wire := wireBlock w 1540 255

def comparePart (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (srcR w) k++
  compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514)++
  maskedConstant g (srcR w) k

def parGates (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  [.CX (w 770) (w 1028)]++(if k%2=1 then [.CX g (w 1028)] else [])++[.CX (w 514) (w 1028)]++
  [.CX (w 1028) (w 770)]++(if k%2=1 then [.CX g (w 770)] else [])++[.CX (w 514) (w 770)]

def prodPart (w : Nat → Wire) (g : Wire) : Program :=
  [.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)]

def c1 (k : Nat) : Nat := tk k false false false
def cg (k : Nat) : Nat := tk k true false false ^^^ tk k false false false
def cf (k : Nat) : Nat := tk k true true false ^^^ tk k true false false
def cp (k : Nat) : Nat := tk k false false true ^^^ tk k false false false
def cgp (k : Nat) : Nat :=
  tk k true false true ^^^ tk k true false false ^^^ tk k false false true ^^^ tk k false false false
def cfp (k : Nat) : Nat :=
  tk k true true true ^^^ tk k true true false ^^^ tk k true false true ^^^ tk k true false false

def loadK (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  xorConstant (hR w) (c1 k)++maskedConstant g (hR w) (cg k)++maskedConstant (w 514) (hR w) (cf k)++
  maskedConstant (w 1028) (hR w) (cp k)++maskedConstant (w 721) (hR w) (cgp k)++
  maskedConstant (w 722) (hR w) (cfp k)

def kAddM (w : Nat → Wire) : Program := mappedAdd (mappedRead (hR w) false) (kR w) (aC w) (w 1797)

def dBits (w : Nat → Wire) : List MappedBit := (List.range 257).map (fun j =>
  let a := (2^257-p).testBit j
  let b := p.testBit j
  if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some (w 1028),flip:=a})

def hAddM (w : Nat → Wire) : Program := mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)

/-- `hAddM` with its first carry trimmed. The first mapped bit is the literal `1`
(`2^257-p` and `p` are both odd) and the carry-in `w 1797` is clean, so the first
majority's Toffoli `CCX (w 1) (w 1797) (w 1540)` never fires; it is dropped. -/
def hPost (w : Nat → Wire) : Program :=
  mappedAdd (dBits w).tail (hpR w).tail (hC2 w).tail (w 1540) ++
    mappedEraseCarry {wire:=none,flip:=true} (w 1) (w 1797) (w 1540) ++
    mappedSum {wire:=none,flip:=true} (w 1) (w 1797)

def hAddT (w : Nat → Wire) : Program := [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ hPost w


def thrA (k : Nat) : Nat := (k+1)/2
def thrB (k : Nat) : Nat := (k+1)/2 ^^^ (k+p+1)/2

def loadT (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (tR w) (thrA k)++maskedConstant (w 721) (tR w) (thrB k)

/-- Unconditional canonical reflection followed by controlled constant addition, merged into the direct first tick. -/
def merged (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  comparePart w g k++(parGates w g k++rotateRight (kR w)++notRegister (kR w))++prodPart w g++loadK w g k++kAddM w++loadK w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddT w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]

/-! ### Layout facts -/

section Layout
variable (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
include hn

theorem mem_blk (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) :
    w i ∈ wireBlock w a n ↔ a ≤ i ∧ i < a + n := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := skywalkPool_index_inj w hn i j hi (by omega) he.symm
    omega
  · intro h
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem w_ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j :=
  index_ne w hn i j hi hj h

omit hn in
theorem blk_sub (a n b m : Nat) (h1 : b≤a) (h2 : a+n≤b+m) : ∀q∈wireBlock w a n,q∈wireBlock w b m := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem blk_nd (a n : Nat) (ha : a+n≤1798) : (wireBlock w a n).Nodup := block_nodup w hn a n ha

theorem blk_dis (a n b m : Nat) (ha : a+n≤1798) (hb : b+m≤1798) (sep : a+n≤b ∨ b+m≤a) :
    List.Disjoint (wireBlock w a n) (wireBlock w b m) := block_disjoint w hn a n b m ha hb sep

theorem g_out (g : Wire) (hg : g∉skywalkPoolWires w) (a n : Nat) (ha : a+n≤1798) : g∉wireBlock w a n :=
  fun h => hg (blk_sub w a n 0 1798 (by omega) (by omega) g h)

theorem g_ne (g : Wire) (hg : g∉skywalkPoolWires w) (i : Nat) (hi : i<1798) : g≠w i := by
  intro e; apply hg; rw [e]
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

end Layout


/-! ### Frame -/

def mutL (w : Nat → Wire) : List Wire := hR w++kR w++tR w++[w 1028,w 514,w 721,w 722]

def MF (w : Nat → Wire) (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState) : Prop :=
  regValue (hR w) s=H ∧ regValue (kR w) s=X ∧ regValue (tR w) s=T ∧
  s (w 1028)=par ∧ s (w 514)=f ∧ s (w 721)=gp ∧ s (w 722)=fp ∧ ∀q,q∉mutL w → s q=b0 q

theorem keep (R : List Wire) (s t : BasisState) (hf : ∀q,q∉R → t q=s q) (C : List Wire)
    (hC : ∀q∈C,q∉R) : regValue C t=regValue C s :=
  regValue_congr C t s (fun q hq => hf q (hC q hq))

section Steps
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem hR_nd : (hR w).Nodup := blk_nd w hn 0 258 (by omega)
theorem kR_nd : (kR w).Nodup := blk_nd w hn 770 258 (by omega)
theorem tR_nd : (tR w).Nodup := blk_nd w hn 1029 256 (by omega)

theorem hR_kR : ∀q∈kR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 770 258 (by omega) (by omega) (by omega)) h hq
theorem hR_tR : ∀q∈tR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem kR_hR : ∀q∈hR w,q∉kR w := fun q hq h => hR_kR w hn q h hq
theorem kR_tR : ∀q∈tR w,q∉kR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 770 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem tR_hR : ∀q∈hR w,q∉tR w := fun q hq h => hR_tR w hn q h hq
theorem tR_kR : ∀q∈kR w,q∉tR w := fun q hq h => kR_tR w hn q h hq

theorem nb (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) (sep : i < a ∨ a + n ≤ i) : w i ∉ wireBlock w a n :=
  block_not_mem w hn i a n hi ha sep

theorem out_of_mut (R : List Wire) (hR' : ∀q∈R,q∈mutL w) (q : Wire) (hq : q∉mutL w) : q∉R :=
  fun h => hq (hR' q h)

theorem hR_mut : ∀q∈hR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem kR_mut : ∀q∈kR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem tR_mut : ∀q∈tR w,q∈mutL w := fun q hq => by simp [mutL,hq]

/-- An operation that changes only the `H` block. -/
theorem stepH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉hR w → t.basis q=s.basis q) (H' : Nat)
    (hv : regValue (hR w) t.basis=H') : MF w b0 H' X T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨hv,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (hR_kR w hn)]; exact h2
  · rw [keep _ _ _ hf _ (hR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 0 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 0 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 0 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 0 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (hR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the `K` block. -/
theorem stepK (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉kR w → t.basis q=s.basis q) (X' : Nat)
    (hv : regValue (kR w) t.basis=X') : MF w b0 H X' T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,hv,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (kR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (kR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 770 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 770 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 770 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (kR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the threshold block. -/
theorem stepT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉tR w → t.basis q=s.basis q) (T' : Nat)
    (hv : regValue (tR w) t.basis=T') : MF w b0 H X T' par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,?_,hv,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (tR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (tR_kR w hn)]; exact h2
  · rw [hf _ (nb w hn 1028 1029 256 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 1029 256 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 1029 256 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 1029 256 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (tR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes one scalar wire `w j` of the frame. -/
theorem stepBit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State) (j : Nat)
    (hj : j=1028 ∨ j=514 ∨ j=721 ∨ j=722)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q≠w j → t.basis q=s.basis q) :
    MF w b0 H X T (if j=1028 then t.basis (w j) else par) (if j=514 then t.basis (w j) else f)
      (if j=721 then t.basis (w j) else gp) (if j=722 then t.basis (w j) else fp) t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have hjr : j<1798 := by omega
  have nh : w j∉hR w := nb w hn j 0 258 hjr (by omega) (by omega)
  have nk : w j∉kR w := nb w hn j 770 258 hjr (by omega) (by omega)
  have nt : w j∉tR w := nb w hn j 1029 256 hjr (by omega) (by omega)
  have ne (i : Nat) (hi : i<1798) (hij : i≠j) : w i≠w j := w_ne w hn i j hi hjr hij
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nh (e ▸ hq)))]; exact h1
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nk (e ▸ hq)))]; exact h2
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nt (e ▸ hq)))]; exact h3
  · by_cases e : j=1028
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 1028 (by omega) (Ne.symm e))]; exact h4
  · by_cases e : j=514
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 514 (by omega) (Ne.symm e))]; exact h5
  · by_cases e : j=721
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 721 (by omega) (Ne.symm e))]; exact h6
  · by_cases e : j=722
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 722 (by omega) (Ne.symm e))]; exact h7
  · intro q hq
    have : q≠w j := by
      intro e; apply hq; rw [e]
      rcases hj with rfl|rfl|rfl|rfl <;> simp [mutL]
    rw [hf q this]; exact h8 q hq

end Steps


/-! ### Concrete steps -/

theorem run_cx (a b : Wire) (m : List Bool) (s : State) :
    run [.CX a b] m s=⟨s.phase,writeBit s.basis b (s.basis b ^^ s.basis a)⟩ := rfl
theorem run_ccx (a b c : Wire) (m : List Bool) (s : State) :
    run [.CCX a b c] m s=⟨s.phase,writeBit s.basis c (s.basis c ^^ (s.basis a && s.basis b))⟩ := rfl
theorem run_x (a : Wire) (m : List Bool) (s : State) :
    run [.X a] m s=⟨s.phase,writeBit s.basis a (!s.basis a)⟩ := rfl

theorem run_meas_and (t a b : Wire) (m : List Bool) (s : State) (ha : a≠t) (hb : b≠t)
    (ht : s.basis t=(s.basis a && s.basis b)) :
    run [.measureX t [] [.CZ a b]] m s=⟨s.phase,writeBit s.basis t false⟩ := by
  simp only [run,measureAndCorrect]
  cases m.headD false <;> simp [correct,writeBit,Function.update_of_ne ha,Function.update_of_ne hb,ht]

section Concrete
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem kR_split (s : BasisState) :
    regValue (kR w) s=(s (w 770)).toNat+2*regValue (wireBlock w 771 257) s := by
  have e : kR w=w 770::wireBlock w 771 257 := by
    simp [kR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 770) <;> simp [regValue,h]

theorem hR_split (s : BasisState) :
    regValue (hR w) s=(s (w 0)).toNat+2*regValue (hpR w) s := by
  have e : hR w=w 0::hpR w := by
    simp [hR,hpR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 0) <;> simp [regValue,h]

theorem hR_src (s : BasisState) :
    regValue (hR w) s=regValue (srcR w) s+2^256*regValue (wireBlock w 256 2) s := by
  have e : hR w=srcR w++wireBlock w 256 2 := by
    rw [hR,srcR,wireBlock_append]
  rw [e,regValue_append,srcR,wireBlock_length]

theorem kR_x (s : BasisState) :
    regValue (kR w) s=regValue (xR w) s+2^256*regValue (wireBlock w 1026 2) s := by
  have e : kR w=xR w++wireBlock w 1026 2 := by
    rw [kR,xR,wireBlock_append]
  rw [e,regValue_append,xR,wireBlock_length]

theorem kR_low (s : BasisState) :
    regValue (kR w) s=regValue (wireBlock w 770 257) s+2^257*regValue (wireBlock w 1027 1) s := by
  have e : kR w=wireBlock w 770 257++wireBlock w 1027 1 := by
    rw [kR,wireBlock_append]
  rw [e,regValue_append,wireBlock_length]

/-- A CX targeting the parity wire. -/
theorem stepParCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 1028) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) :
    Triple (MF w b0 H X T par f gp fp) [.CX c (w 1028)] (MF w b0 H X T (par ^^ cv) f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 1028)
    (s.basis (w 1028) ^^ s.basis c)⟩ 1028 (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit,h.2.2.2.1,hcv s.basis h] using this

/-- A CX targeting bit 0 of the K block. -/
theorem stepLowCX (b0 : BasisState) (H Y T : Nat) (b par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 770) (hcv : ∀s : BasisState,MF w b0 H (2*Y+b.toNat) T par f gp fp s → s c=cv) :
    Triple (MF w b0 H (2*Y+b.toNat) T par f gp fp) [.CX c (w 770)]
      (MF w b0 H (2*Y+(b ^^ cv).toNat) T par f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have m770 : w 770∈kR w := (mem_blk w hn 770 770 258 (by omega) (by omega)).mpr (by omega)
  have rest : ∀q∈wireBlock w 771 257,q≠w 770 := fun q hq e =>
    nb w hn 770 771 257 (by omega) (by omega) (by omega) (e ▸ hq)
  apply stepK w hn b0 H _ T par f gp fp s _ h
  · intro q hq; have : q≠w 770 := fun e => hq (e ▸ m770)
    simp [writeBit,Function.update_of_ne this]
  · have sp := kR_split w hn s.basis
    have sp2 := kR_split w hn (writeBit s.basis (w 770) (s.basis (w 770) ^^ s.basis c))
    rw [h.2.1] at sp
    rw [sp2,regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,Function.update_of_ne (rest q hq)])]
    rw [hcv s.basis h]
    simp only [writeBit,Function.update_self]
    cases hb : s.basis (w 770) <;> cases b <;> cases cv <;> simp [hb] at sp ⊢ <;> omega

end Concrete


section Concrete2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepXorH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (xorConstant (hR w) v) (MF w b0 (H^^^v) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := xorConstant_correct (hR w) (hR_nd w hn) v (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1])⟩

theorem stepMaskH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉hR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (hR w) v)
      (MF w b0 (H^^^(if cv then v else 0)) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (hR w) v (hR_nd w hn) hc
    (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1,hcv s.basis h])⟩

theorem stepMaskT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉tR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^256) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (tR w) v)
      (MF w b0 H X (T^^^(if cv then v else 0)) par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (tR w) v (tR_nd w hn) hc
    (by simpa [tR,wireBlock_length] using hv) s m
  exact ⟨hp,stepT w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.2.2.1,hcv s.basis h])⟩

theorem stepCCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (a b : Wire) (j : Nat)
    (hj : j=721 ∨ j=722) (av bv : Bool) (ha : a≠w j) (hb : b≠w j)
    (hav : ∀s : BasisState,MF w b0 H X T par f gp fp s → s a=av)
    (hbv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s b=bv) :
    Triple (MF w b0 H X T par f gp fp) [.CCX a b (w j)]
      (MF w b0 H X T par f (if j=721 then gp ^^ (av && bv) else gp)
        (if j=722 then fp ^^ (av && bv) else fp)) := by
  intro s m h
  rw [run_ccx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w j)
    (s.basis (w j) ^^ (s.basis a && s.basis b))⟩ j (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  rcases hj with rfl|rfl
  · simpa [writeBit,h.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this
  · simpa [writeBit,h.2.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this

theorem stepKAdd (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 H X T par f gp fp) (kAddM w) (MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m h
  have caway : ∀q∈aC w,q∉mutL w := by
    intro q hq hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
    · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
    all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm
  have m1797 : w 1797∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have nd : (w 1797::(kR w++aC w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),
      blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
  have src : ∀q∈mappedWires (mappedRead (hR w) false),q∉w 1797::(kR w++aC w) := by
    rw [mappedRead_wires]
    intro q hq hm
    simp only [List.mem_cons,List.mem_append] at hm
    rcases hm with e|e|e
    · exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq)
    · exact hR_kR w hn q e hq
    · exact List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq e
  have cl : ∀q∈aC w,s.basis q=false := fun q hq => (h.2.2.2.2.2.2.2 q (caway q hq)).trans (hc q hq)
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (mappedRead (hR w) false) (kR w) (aC w) (w 1797) nd src
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length]) s m cl
  refine ⟨hp,stepK w hn b0 H X T par f gp fp s _ h he _ ?_⟩
  rw [hval,mappedRead_value,h.1,h.2.1,(h.2.2.2.2.2.2.2 _ m1797).trans hcin]
  simp [kR,wireBlock_length]

end Concrete2


def CF (w : Nat → Wire) (b0 : BasisState) (S : Nat) (F : Bool) (s : BasisState) : Prop :=
  regValue (srcR w) s=S ∧ s (w 514)=F ∧ ∀q,q∉srcR w → q≠w 514 → s q=b0 q

section Compare
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem src_nd : (srcR w).Nodup := blk_nd w hn 0 256 (by omega)
theorem w514_src : w 514∉srcR w := nb w hn 514 0 256 (by omega) (by omega) (by omega)

theorem cfMask (b0 : BasisState) (S : Nat) (F : Bool) (c : Wire) (hc : c∉srcR w) (hc' : c≠w 514)
    (v : Nat) (hv : v<2^256) :
    Triple (CF w b0 S F) (maskedConstant c (srcR w) v) (CF w b0 (S^^^(if b0 c then v else 0)) F) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (srcR w) v (src_nd w hn) hc
    (by simpa [srcR,wireBlock_length] using hv) s m
  refine ⟨hp,?_,?_,?_⟩
  · rw [hval,h.1,h.2.2 c hc hc']
  · rw [he _ (w514_src w hn)]; exact h.2.1
  · intro q h1 h2; rw [he q h1]; exact h.2.2 q h1 h2

theorem cfNot (b0 : BasisState) (S : Nat) (F : Bool) :
    Triple (CF w b0 S F) (notRegister (srcR w)) (CF w b0 (2^256-1-S) F) := by
  intro s m h
  rw [notRegister_correct (srcR w) (src_nd w hn)]
  refine ⟨rfl,?_,?_,?_⟩
  · change regValue (srcR w) (fun q => if q∈srcR w then !s.basis q else s.basis q)=_
    rw [regValue_congr (srcR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,h.1]
    simp [srcR,wireBlock_length]
  · change (if w 514∈srcR w then !s.basis (w 514) else s.basis (w 514))=_
    simp [w514_src w hn,h.2.1]
  · intro q h1 h2
    change (if q∈srcR w then !s.basis q else s.basis q)=_
    simp [h1,h.2.2 q h1 h2]

theorem cfCmp (b0 : BasisState) (S : Nat) (F : Bool) (X : Nat) (hx : regValue (xR w) b0=X)
    (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false) :
    Triple (CF w b0 S F) (compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514))
      (CF w b0 S (F ^^ decide (X<S))) := by
  intro s m h
  have xs : ∀q∈xR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)) h' hq
  have x514 : ∀q∈xR w,q≠w 514 := fun q hq e => nb w hn 514 770 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have cs : ∀q∈cR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)) h' hq
  have c514 : ∀q∈cR w,q≠w 514 := fun q hq e => nb w hn 514 256 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have n513 : w 513∉srcR w := nb w hn 513 0 256 (by omega) (by omega) (by omega)
  have e513 : w 513≠w 514 := w_ne w hn 513 514 (by omega) (by omega) (by omega)
  have nd : (w 514::w 513::(xR w++srcR w++cR w)).Nodup := by
    have a1 := blk_dis w hn 770 256 0 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
    have l1 : (xR w++srcR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 770 256 (by omega),src_nd w hn,a1⟩
    have l2 : (xR w++srcR w++cR w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨e513.symm,⟨nb w hn 514 770 256 (by omega) (by omega) (by omega),w514_src w hn⟩,
        nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 513 770 256 (by omega) (by omega) (by omega),n513⟩,
        nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hv⟩ := compareLt_correct none (xR w) (srcR w) (cR w) (w 513) (w 514) nd (by simp)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,srcR,xR,wireBlock_length]) s m
    ((h.2.2 _ n513 e513).trans hcin) (fun q hq => (h.2.2 q (cs q hq) (c514 q hq)).trans (hc q hq))
  refine ⟨hp,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => he q (fun e => w514_src w hn (e ▸ hq)))]; exact h.1
  · rw [hv,h.2.1,h.1,regValue_congr _ _ b0 (fun q hq => h.2.2 q (xs q hq) (x514 q hq)),hx]
    simp [controlValue]
  · intro q h1 h2; rw [he q h2]; exact h.2.2 q h1 h2

theorem cfCompare (b0 : BasisState) (F : Bool) (k X : Nat) (hk : k<2^256)
    (hx : regValue (xR w) b0=X) (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) :
    Triple (CF w b0 0 F) (comparePart w g k)
      (CF w b0 0 (F ^^ decide (X<(if b0 g then k else 0)))) := by
  have t := ((cfMask w hn b0 0 F g gs g514 k hk).seq
    (cfCmp w hn b0 _ F X hx hc hcin)).seq
    (cfMask w hn b0 _ _ g gs g514 k hk)
  simpa only [comparePart,Nat.zero_xor,Nat.xor_self] using t

end Compare


def dScalar (par : Bool) : Nat :=
  (List.range 257).foldr (fun j acc => (if par then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0

theorem dScalar_value (par : Bool) : dScalar par=delta par := by
  cases par <;> decide

private theorem selected_bit_value (flag : Wire) (a b : Bool) (s : BasisState) :
    (if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a}).value s=if s flag then b else a := by
  cases a <;> cases b <;> cases hf : s flag <;> simp [MappedBit.value,hf]

private theorem d_list_value (is : List Nat) (flag : Wire) (s : BasisState) :
    mappedValue (is.map (fun j =>
      let a := (2^257-p).testBit j
      let b := p.testBit j
      if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some flag,flip:=a})) s=
      is.foldr (fun j acc => (if s flag then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih,selected_bit_value]

theorem dBits_value (w : Nat → Wire) (s : BasisState) : mappedValue (dBits w) s=delta (s (w 1028)) := by
  rw [dBits,d_list_value]
  exact dScalar_value (s (w 1028))

theorem dBits_length (w : Nat → Wire) : (dBits w).length=257 := by simp [dBits]

theorem dBits_cons (w : Nat → Wire) :
    ∃ b' bs, dBits w = {wire:=none,flip:=true} :: b' :: bs := by
  have e : List.range 257 = 0 :: 1 :: List.range' 2 255 := by
    rw [List.range_eq_range']; rfl
  have t1 : (2^257-p).testBit 0 = true := by rw [p_val]; decide
  have t2 : p.testBit 0 = true := by rw [p_val]; decide
  rw [dBits, e, List.map_cons, List.map_cons]
  simp only [t1, t2, ite_true]
  exact ⟨_, _, rfl⟩

theorem hpR_cons (w : Nat → Wire) : ∃ y' ys, hpR w = w 1 :: y' :: ys :=
  ⟨w 2, (List.range' 3 255).map w, by
    rw [hpR, wireBlock, show (257:Nat) = 255+1+1 from rfl, List.range'_succ, List.range'_succ]; rfl⟩

theorem hC2_cons (w : Nat → Wire) : ∃ cs, hC2 w = w 1540 :: cs :=
  ⟨(List.range' 1541 255).map w, by
    rw [hC2, wireBlock, show (256:Nat) = 255+1 from rfl, List.range'_succ]; rfl⟩

theorem hAddM_split (w : Nat → Wire) :
    hAddM w = [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ [.CCX (w 1) (w 1797) (w 1540)] ++ hPost w := by
  obtain ⟨b', bs, hD⟩ := dBits_cons w
  obtain ⟨y', ys, hY⟩ := hpR_cons w
  obtain ⟨cs, hC⟩ := hC2_cons w
  simp only [hAddM, hPost, hD, hY, hC, List.tail_cons, mappedAdd, mappedMajority, List.append_assoc,
    List.cons_append, List.nil_append, if_true]

/-- Dropping a Toffoli whose second control is false after a measurement-free prefix. -/
theorem run_drop_ccx (P Q : Program) (a b t : Wire) (m : List Bool) (s : State)
    (hP : measurementCount P = 0) (hb : (run P [] s).basis b = false) :
    run (P ++ [.CCX a b t] ++ Q) m s = run (P ++ Q) m s := by
  rw [List.append_assoc, run_append, run_append P Q, hP]
  simp only [List.take_zero, List.drop_zero, List.cons_append, List.nil_append, run, hb,
    Bool.and_false, Bool.xor_false, writeBit, Function.update_eq_self]

theorem hAddT_run (w : Nat → Wire) (h17 : w 1797 ≠ w 1540) (m : List Bool) (s : State)
    (hc : s.basis (w 1797) = false) : run (hAddT w) m s = run (hAddM w) m s := by
  rw [hAddM_split, hAddT, run_drop_ccx]
  · rfl
  · simp only [run, writeBit, Function.update_of_ne h17, hc]

theorem hAddT_counts (w : Nat → Wire) :
    toffoliCount (hAddT w) + 1 = toffoliCount (hAddM w) ∧
      measurementCount (hAddT w) = measurementCount (hAddM w) := by
  rw [hAddM_split, hAddT]
  simp only [toffoliCount_append, measurementCount_append]
  constructor
  · simp [toffoliCount]; omega
  · simp [measurementCount]

theorem hAddT_wires (w : Nat → Wire) : wires (hAddT w) ⊆ wires (hAddM w) := by
  rw [hAddM_split, hAddT]
  simp only [wires_append]
  exact Finset.union_subset_union (Finset.subset_union_left) (Finset.Subset.refl _)

theorem hAddT_physical (w : Nat → Wire) (h : GatePhysical (hAddM w)) : GatePhysical (hAddT w) := by
  rw [hAddM_split] at h
  rw [hAddT]
  simp only [gatePhysical_append] at h ⊢
  exact ⟨h.1.1, h.2⟩

theorem hAddT_slots (w : Nat → Wire) :
    Challenge.gateSlots (hAddT w) + 1 = Challenge.gateSlots (hAddM w) := by
  rw [hAddM_split, hAddT]
  simp only [Challenge.gateSlots_append]
  simp [Challenge.gateSlots, Challenge.instructionSlots]
  omega


theorem dBits_wire (w : Nat → Wire) (q : Wire) (hq : q∈mappedWires (dBits w)) : q=w 1028 := by
  simp only [dBits,mappedWires,List.mem_flatMap,List.mem_map] at hq
  obtain ⟨b,⟨j,_,rfl⟩,hb⟩ := hq
  split at hb <;> simp_all

section Rest
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepCompareMF (b0 : BasisState) (k X : Nat) (hk : k<2^256) (hX : X<2^256)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) (gm : g∉mutL w) :
    Triple (MF w b0 0 X 0 false false false false) (comparePart w g k)
      (MF w b0 0 X 0 false (decide (X<(if b0 g then k else 0))) false false) := by
  intro s m h
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have sp := hR_src w hn s.basis
  have kx := kR_x w hn s.basis
  have xl := regValue_lt (xR w) s.basis
  have sl := regValue_lt (srcR w) s.basis
  simp only [xR,srcR,wireBlock_length] at xl sl
  rw [h1] at sp; rw [h2] at kx
  have hx : regValue (xR w) s.basis=X := by
    have : regValue (wireBlock w 1026 2) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 1026 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 1026 2) s.basis := Nat.le_mul_of_pos_right _ this
      omega
    omega
  have src0 : regValue (srcR w) s.basis=0 := by omega
  have top0 : regValue (wireBlock w 256 2) s.basis=0 := by
    by_contra hne; have : 1≤regValue (wireBlock w 256 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
    have : 2^256≤2^256*regValue (wireBlock w 256 2) s.basis := Nat.le_mul_of_pos_right _ this
    omega
  have hzero := (regValue_zero _ _).mp h1
  have cc : ∀q∈cR w,s.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    by_cases hi2 : i<258
    · exact hzero _ ((mem_blk w hn i 0 258 (by omega) (by omega)).mpr (by omega))
    · rw [h8 _ ?_]; exact hc i (by omega) (by omega)
      simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
      refine ⟨⟨⟨nb w hn i 0 258 (by omega) (by omega) (by omega),nb w hn i 770 258 (by omega) (by omega) (by omega)⟩,
        nb w hn i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
        exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have m513 : w 513∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 513 0 258 (by omega) (by omega) (by omega),nb w hn 513 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 513 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have cfr := cfCompare w g hn s.basis false k X hk hx cc ((h8 _ m513).trans hcin) gs g514 s m
    ⟨src0,h5,fun _ _ _ => rfl⟩
  obtain ⟨tp,c1',c2',c3'⟩ := cfr
  refine ⟨tp,?_⟩
  simp only [Bool.false_xor] at c2'
  have gv : s.basis g=b0 g := h8 g gm
  rw [gv] at c2'
  have same : ∀q,q∉srcR w → q≠w 514 → (run (comparePart w g k) m s).basis q=s.basis q := c3'
  have srcm : ∀q∈srcR w,q∈mutL w := fun q hq => hR_mut w hn q (blk_sub w 0 256 0 258 (by omega) (by omega) q hq)
  have m514 : w 514∈mutL w := by simp [mutL]
  refine ⟨?_,?_,?_,?_,c2',?_,?_,?_⟩
  · rw [hR_src w hn,c1',regValue_congr _ _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 256 2 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 256 2 (by omega) (by omega) (by omega) (e ▸ hq))),top0]; simp
  · rw [regValue_congr (kR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 770 258 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 770 258 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h2
  · rw [regValue_congr (tR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 1029 256 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 1029 256 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h3
  · rw [same _ (nb w hn 1028 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h4
  · rw [same _ (nb w hn 721 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h6
  · rw [same _ (nb w hn 722 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h7
  · intro q hq
    rw [same q (fun h' => hq (srcm q h')) (fun e => hq (e ▸ m514))]; exact h8 q hq

theorem stepMeasFp (b0 : BasisState) (H X T : Nat) (par f gp : Bool) :
    Triple (MF w b0 H X T par f gp (f && par)) [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]
      (MF w b0 H X T par f gp false) := by
  intro s m h
  rw [run_meas_and (w 722) (w 514) (w 1028) m s (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.2.1,h.2.2.2.2.1,h.2.2.2.1])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp (f && par) s ⟨s.phase,writeBit s.basis (w 722) false⟩ 722
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepMeasGp (b0 : BasisState) (H X T : Nat) (par f fp : Bool) (gm : g∉mutL w)
    (g515 : g≠w 721) :
    Triple (MF w b0 H X T par f (b0 g && par) fp) [.measureX (w 721) [] [.CZ g (w 1028)]]
      (MF w b0 H X T par f false fp) := by
  intro s m h
  rw [run_meas_and (w 721) g (w 1028) m s g515
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.1,h.2.2.2.1,h.2.2.2.2.2.2.2 g gm])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f (b0 g && par) fp s ⟨s.phase,writeBit s.basis (w 721) false⟩ 721
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepCopy (b0 : BasisState) (X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 X T par f gp fp) (copyRegister none (wireBlock w 770 257) (hpR w))
      (MF w b0 (2*(X%2^257)) X T par f gp fp) := by
  intro s m h
  have nd : (wireBlock w 770 257++hpR w).Nodup := List.nodup_append'.mpr
    ⟨blk_nd w hn 770 257 (by omega),blk_nd w hn 1 257 (by omega),
      blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hval⟩ := copyRegister_correct none (wireBlock w 770 257) (hpR w)
    (by simp [hpR,wireBlock_length]) nd (by simp) s m
  refine ⟨hp,stepH w hn b0 0 X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (copyRegister none (wireBlock w 770 257) (hpR w)) m s).basis
    have kl := kR_low w hn s.basis
    have ll := regValue_lt (wireBlock w 770 257) s.basis
    simp only [wireBlock_length] at ll
    rw [h.1] at sp; rw [h.2.1] at kl
    rw [sp2,hval,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega))]
    simp only [copyValue]
    have e0 : regValue (hpR w) s.basis=0 := by omega
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    rw [e0,b0',Nat.zero_xor]
    have : regValue (wireBlock w 770 257) s.basis=X%2^257 := by omega
    rw [this]; simp

end Rest


section Rest2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem aC_out : ∀q∈aC w,q∉mutL w := by
  intro q hq hm
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
  · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
  all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm

theorem w1797_out : w 1797∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
    nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
    exact w_ne w hn _ _ (by omega) (by omega) (by omega)

theorem stepHAdd (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddM w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  rw [hAddM]
  have nd : (w 1797::(hpR w++hC2 w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),
      blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
  have srcw : ∀q∈mappedWires (dBits w),q∉w 1797::(hpR w++hC2 w) := by
    intro q hq
    rw [dBits_wire w q hq]
    simp only [List.mem_cons,List.mem_append,not_or]
    exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
      nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC2 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 256 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (dBits w) (hpR w) (hC2 w) (w 1797) nd srcw
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length]) s m cl
  refine ⟨hp,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)) m s).basis
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have e0 : regValue (hpR w) s.basis=Y := by rw [b0'] at sp; simp at sp; omega
    rw [sp2,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega)),b0',hval,dBits_value,e0,
      h.2.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin]
    simp [hpR,wireBlock_length]

theorem stepHAddT (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddT w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  have c17 : s.basis (w 1797)=false := (h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin
  rw [hAddT_run w (w_ne w hn 1797 1540 (by omega) (by omega) (by omega)) m s c17]
  exact stepHAdd w hn b0 Y X T par f gp fp hY hc hcin s m h

theorem stepW0 (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 (2*Y) X T par f gp fp) [.CX (w 1028) (w 0),.X (w 0)]
      (MF w b0 (2*Y+(!par).toNat) X T par f gp fp) := by
  intro s m h
  have e : run [.CX (w 1028) (w 0),.X (w 0)] m s=⟨s.phase,writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028)))⟩ := by
    simp [run,writeBit]
  rw [e]
  refine ⟨rfl,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq
    have : q≠w 0 := fun e' => hq (e' ▸ (mem_blk w hn 0 0 258 (by omega) (by omega)).mpr (by omega))
    simp [writeBit,Function.update_of_ne this]
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have rest : regValue (hpR w) (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))=
        regValue (hpR w) s.basis := regValue_congr _ _ _ (fun q hq => by
      have : q≠w 0 := fun e' => nb w hn 0 1 257 (by omega) (by omega) (by omega) (e' ▸ hq)
      simp [writeBit,Function.update_of_ne this])
    rw [sp2,rest,b0',h.2.2.2.1]
    rw [b0'] at sp
    simp [writeBit] at sp ⊢
    omega

theorem stepErase (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) (hH : H<2^257) (hf : f=decide (H/2<T)) :
    Triple (MF w b0 H X T par f gp fp) (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))
      (MF w b0 H X T par false gp fp) := by
  intro s m h
  have nd : (w 514::w 1797::(hp8 w++tR w++hC3 w)).Nodup := by
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),⟨nb w hn 514 1 256 (by omega) (by omega) (by omega),
        nb w hn 514 1029 256 (by omega) (by omega) (by omega)⟩,nb w hn 514 1540 255 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC3 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 255 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have sp := hR_split w hn s.basis
  rw [h.1] at sp
  have e8 : hpR w=hp8 w++wireBlock w 257 1 := by rw [hpR,hp8,wireBlock_append]
  have sp8 := regValue_append (hp8 w) (wireBlock w 257 1) s.basis
  rw [←e8] at sp8
  have l8 := regValue_lt (hp8 w) s.basis
  simp only [hp8,wireBlock_length] at sp8 l8
  have hpv : regValue (hp8 w) s.basis=H/2 := by
    have : regValue (wireBlock w 257 1) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 257 1) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 257 1) s.basis := Nat.le_mul_of_pos_right _ this
      cases hb : s.basis (w 0) <;> simp [hb] at sp <;> omega
    cases hb : s.basis (w 0) <;> simp [hb] at sp <;> simp only [hp8] at * <;> omega
  have r := eraseLtChain_correct (hp8 w) (tR w) (hC3 w) (w 1797) (w 514) nd
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length]) s m cl
    (by rw [h.2.2.2.2.1,hpv,h.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin,hf]; simp)
  rw [r]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 514) false⟩ 514
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

end Rest2


section Compose
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem g_mut (hg : g∉skywalkPoolWires w) : g∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨g_out w hn g hg 0 258 (by omega),g_out w hn g hg 770 258 (by omega)⟩,g_out w hn g hg 1029 256 (by omega)⟩,
    g_ne w hn g hg 1028 (by omega),g_ne w hn g hg 514 (by omega),g_ne w hn g hg 721 (by omega),g_ne w hn g hg 722 (by omega)⟩

theorem low_bit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState)
    (h : MF w b0 H X T par f gp fp s) : s (w 770)=decide (X%2=1) := by
  have sp := kR_split w hn s
  rw [h.2.1] at sp
  cases hb : s (w 770) <;> simp [hb] at sp ⊢ <;> omega

omit hn in
theorem xor_clear (a b c : Bool) : (((a ^^ (((false ^^ a) ^^ b) ^^ c)) ^^ b) ^^ c)=false := by
  cases a <;> cases b <;> cases c <;> rfl
omit hn in
theorem xor_clear2 (a c : Bool) : ((a ^^ ((false ^^ a) ^^ c)) ^^ c)=false := by
  cases a <;> cases c <;> rfl

theorem stepPar (b0 : BasisState) (k X : Nat) (f : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 0 X 0 false f false false) (parGates w g k)
      (MF w b0 0 (2*(X/2)) 0 (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f) f false false) := by
  have gm := g_mut w g hn hg
  have g1028 : g≠w 1028 := g_ne w hn g hg 1028 (by omega)
  have g770 : g≠w 770 := g_ne w hn g hg 770 (by omega)
  have e1 : w 770≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e2 : w 514≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e3 : w 1028≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e4 : w 514≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have gv (H X T : Nat) (par f gp fp : Bool) : ∀s : BasisState,MF w b0 H X T par f gp fp s → s g=b0 g :=
    fun s h => h.2.2.2.2.2.2.2 g gm
  have xs : X=2*(X/2)+(decide (X%2=1)).toNat := by
    rcases Nat.mod_two_eq_zero_or_one X with hx|hx <;> simp [hx] <;> omega
  apply Triple.conseq (fun s h => by rw [xs] at h; exact h) ?_ (fun s h => h)
  by_cases hk : k%2=1
  · rw [parGates,if_pos hk,if_pos hk]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false g (b0 g) g1028 (gv _ _ _ _ _ _ _)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 _ _ f false false g (b0 g) g770 (gv _ _ _ _ _ _ _)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear] at h
    simpa [hk] using h
  · rw [parGates,if_neg hk,if_neg hk]
    try simp only [List.nil_append]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear2] at h
    simpa [hk] using h

theorem stepRot (b0 : BasisState) (X : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 (2*(X/2)) 0 par f gp fp) (rotateRight (kR w)) (MF w b0 0 (X/2) 0 par f gp fp) := by
  intro s m h
  have r := rotateRight_spec (kR w) (kR_nd w hn) (2*(X/2)) (by omega) s m h.2.1
  have fr := rotate_frame (kR w) s m
  refine ⟨r.1,stepK w hn b0 0 _ 0 par f gp fp s _ h fr.2.1 _ ?_⟩
  have := r.2
  change regValue (kR w) _=_ at this
  rw [this]; omega

end Compose


/-- Complement the entire 258-bit K bank after shifting the original input. -/
theorem stepNotK (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 H X T par f gp fp) (notRegister (kR w))
      (MF w b0 H (2^258-1-X) T par f gp fp) := by
  intro s m hs
  rw [notRegister_correct (kR w) (kR_nd w hn)]
  refine ⟨rfl,?_⟩
  apply stepK w hn b0 H X T par f gp fp s _ hs
  · intro q hq
    change (if q∈kR w then !s.basis q else s.basis q)=s.basis q
    simp only [if_neg hq]
  · change regValue (kR w) (fun q => if q∈kR w then !s.basis q else s.basis q)=_
    rw [regValue_congr (kR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,hs.2.1]
    simp [kR,wireBlock_length]

theorem kC_lt (par : Bool) : kConstant false par<2^258 := by
  cases par <;> norm_num [kConstant,ECDSAAdd.p]

theorem tk_lt (k : Nat) (G f par : Bool) : tk k G f par<2^258 := by
  unfold tk
  split_ifs <;> first | exact Nat.mod_lt _ (by norm_num) | norm_num

theorem xlt (a b : Nat) (ha : a<2^258) (hb : b<2^258) : a^^^b<2^258 := Nat.xor_lt_two_pow ha hb

theorem c1_lt (k : Nat) : c1 k<2^258 := tk_lt k _ _ _
theorem cg_lt (k : Nat) : cg k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cf_lt (k : Nat) : cf k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cp_lt (k : Nat) : cp k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cgp_lt (k : Nat) : cgp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)
theorem cfp_lt (k : Nat) : cfp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)

def lkv (k : Nat) (G f par gp fp : Bool) : Nat :=
  c1 k ^^^ (if G then cg k else 0) ^^^ (if f then cf k else 0) ^^^ (if par then cp k else 0) ^^^
    (if gp then cgp k else 0) ^^^ (if fp then cfp k else 0)

theorem lkv_eq (k : Nat) (G f par : Bool) (hfg : f=true → G=true) :
    lkv k G f par (G && par) (f && par)=tk k G f par := by
  cases G <;> cases f <;> cases par <;> simp at hfg <;>
    simp [lkv,c1,cg,cf,cp,cgp,cfp,Nat.xor_assoc,Nat.xor_comm,Nat.xor_left_comm,Nat.xor_self]

def ltv (k : Nat) (G gp : Bool) : Nat := (if G then thrA k else 0) ^^^ (if gp then thrB k else 0)

theorem ltv_eq (k : Nat) (G par : Bool) : ltv k G (G && par)=thr k G par := by
  cases G <;> cases par <;> simp [ltv,thr,thrA,thrB,Nat.xor_assoc,Nat.xor_self]

section Compose2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepLoadK (b0 : BasisState) (k H X T : Nat) (par f gp fp : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadK w g k)
      (MF w b0 (H^^^lkv k (b0 g) f par gp fp) X T par f gp fp) := by
  have gm := g_mut w g hn hg
  have gh : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h515 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h516 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t := (stepXorH w hn b0 H X T par f gp fp (c1 k) (c1_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp g (b0 g) gh (fun s h => h.2.2.2.2.2.2.2 g gm) (cg k) (cg_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 514) f h514 (fun s h => h.2.2.2.2.1) (cf k) (cf_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 1028) par h1028 (fun s h => h.2.2.2.1) (cp k) (cp_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (cgp k) (cgp_lt k)).seq
    (stepMaskH w hn b0 _ X T par f gp fp (w 722) fp h516 (fun s h => h.2.2.2.2.2.2.1) (cfp k) (cfp_lt k))))))
  unfold loadK
  simp only [List.append_assoc]
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have e : H^^^c1 k^^^(if b0 g then cg k else 0)^^^(if f then cf k else 0)^^^(if par then cp k else 0)^^^
      (if gp then cgp k else 0)^^^(if fp then cfp k else 0)=H^^^lkv k (b0 g) f par gp fp := by
    simp only [lkv,Nat.xor_assoc]
  rw [e] at h; exact h

theorem stepLoadT (b0 : BasisState) (k H X T : Nat) (hk : k<p) (par f gp fp : Bool)
    (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadT w g k)
      (MF w b0 H X (T^^^ltv k (b0 g) gp) par f gp fp) := by
  have gm := g_mut w g hn hg
  have gt : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have h515 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  rw [p_val] at hk
  have la : thrA k<2^256 := by unfold thrA; omega
  have lb : thrB k<2^256 := Nat.xor_lt_two_pow la (by rw [p_val]; omega)
  have t := (stepMaskT w hn b0 H X T par f gp fp g (b0 g) gt (fun s h => h.2.2.2.2.2.2.2 g gm) (thrA k) la).seq
    (stepMaskT w hn b0 H X _ par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (thrB k) lb)
  unfold loadT
  apply Triple.conseq (fun _ h => h) t
  intro s h
  simpa only [ltv,Nat.xor_assoc] using h

end Compose2


section Main
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (hac : ∀q∈aC w,b0 q=false) (h1797 : b0 (w 1797)=false) :
    let G := b0 g
    let f := decide (X<(if G then k else 0))
    let dx := (p-1-X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    Triple (MF w b0 0 X 0 false false false false) (merged w g k)
      (MF w b0 (2*H+(!par).toNat) K 0 par false false false) := by
  intro G f dx par K H
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX G
  change decide (X%2=1)=x0 k G f par at a1
  change (2^258-1-X/2+tk k G f par)%2^258=K at a2
  change H=dx/2+(if par then hConstant else 0) at a3
  change f=decide (H<thr k G par) at a4
  have gm := g_mut w g hn hg
  have hp' := p_val
  have hpar : (decide (X%2=1) ^^ (G && decide (k%2=1)) ^^ f)=par := by
    have e : decide (X%2=1)=x0 k G f par := a1
    rw [e]; unfold x0 ksel0
    generalize (G && decide (k%2=1))=a
    cases par <;> cases a <;> cases f <;> rfl
  have hfg : f=true → G=true := by
    intro hf; cases hG : G
    · have : f=false := by
        simp only [f,hG,Bool.false_eq_true,if_false,decide_eq_false_iff_not]; rw [p_val] at hX; omega
      rw [this] at hf; exact absurd hf (by simp)
    · rfl
  have fC : decide (X<(if b0 g then k else 0))=f := by simp [f,G,cmpC]
  have s1 := stepCompareMF w g hn b0 k X (by rw [p_val] at hk; omega) (by rw [p_val] at hX; omega)
    hc hcin (g_out w hn g hg 0 256 (by omega)) (g_ne w hn g hg 514 (by omega)) gm
  rw [fC] at s1
  have s2 := stepPar w g hn b0 k X f hg
  rw [show (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f)=par from hpar] at s2
  have s3 := stepRot w hn b0 X par f false false
  have s3n := stepNotK w hn b0 0 (X/2) 0 par f false false
  have s4a := stepCCX w hn b0 0 (2^258-1-X/2) 0 par f false false g (w 1028) 721 (by omega) G par
    (g_ne w hn g hg 721 (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 g gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s4a
  have s4b := stepCCX w hn b0 0 (2^258-1-X/2) 0 par f (G && par) false (w 514) (w 1028) 722 (by omega) f par
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s4b
  have s5 := stepLoadK w g hn b0 k 0 (2^258-1-X/2) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 g=G from rfl,lkv_eq k G f par hfg] at s5
  have s6 := stepKAdd w hn b0 (tk k G f par) (2^258-1-X/2) 0 par f (G && par) (f && par) hac h1797
  rw [show (tk k G f par+(2^258-1-X/2))%2^258=K by rw [Nat.add_comm]; exact a2] at s6
  have s7 := stepLoadK w g hn b0 k (tk k G f par) K 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkv_eq k G f par hfg,Nat.xor_self] at s7
  have s8 := stepMeasFp w hn b0 0 K 0 par f (G && par)
  have s9 := stepCopy w hn b0 K 0 par f (G && par) false
  have s10 := stepHAddT w hn b0 (K%2^257) K 0 par f (G && par) false (Nat.mod_lt _ (by norm_num)) hac h1797
  rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]] at s10
  have s11 := stepW0 w hn b0 H K 0 par f (G && par) false
  have s12 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K 0 hk par f (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltv_eq] at s12
  have hHlt : 2*H+(!par).toNat<2^257 := by
    have dxl : dx<p := Nat.mod_lt _ (by rw [p_val]; norm_num)
    rw [a3]; rw [p_val] at dxl
    cases par <;> simp [hC_val] <;> omega
  have s13 := stepErase w hn b0 (2*H+(!par).toNat) K (thr k G par) par f (G && par) false hac h1797 hHlt
    (by rw [show (2*H+(!par).toNat)/2=H by cases par <;> simp <;> omega]; exact a4)
  have s14 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K (thr k G par) hk par false (G && par) false hg
  rw [show b0 g=G from rfl,ltv_eq,Nat.xor_self] at s14
  have s15 := stepMeasGp w g hn b0 (2*H+(!par).toNat) K 0 par false false gm (g_ne w hn g hg 721 (by omega))
  have t := s1.seq (s2.seq ((s3.seq s3n).seq (s4a.seq (s4b.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    (s11.seq (s12.seq (s13.seq (s14.seq s15))))))))))))))
  unfold merged prodPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

end Main


section Final
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

/-- The reflected-input merged circuit leaves exactly the direct-first-tick state for
`(p-1-X+g*k) mod p`, on every measurement record. -/
theorem merged_eq_forward (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (t u : State) (m m' : List Bool)
    (tk0 : regValue (kR w) t.basis=X) (th0 : regValue (hR w) t.basis=0) (tt0 : regValue (tR w) t.basis=0)
    (t1028 : t.basis (w 1028)=false) (t514 : t.basis (w 514)=false) (t515 : t.basis (w 721)=false)
    (t516 : t.basis (w 722)=false)
    (hc : ∀ i, 258 ≤ i → i < 512 → t.basis (w i) = false) (hcin : t.basis (w 513)=false)
    (hac : ∀q∈aC w,t.basis q=false) (h1797 : t.basis (w 1797)=false)
    (hu : u.phase=t.phase) (hu2 : ∀q,q∉kR w → u.basis q=t.basis q)
    (hu3 : regValue (kR w) u.basis=(p-1-X+(if t.basis g then k else 0))%p) :
    run (merged w g k) m t=run (NativeFirstDirect.forward w) m' u := by
  have mf0 : MF w t.basis 0 X 0 false false false false t.basis :=
    ⟨th0,tk0,tt0,t1028,t514,t515,t516,fun _ _ => rfl⟩
  have tri := merged_triple w g hn hg k hk t.basis X hX hc hcin hac h1797 t m mf0
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX (t.basis g)
  generalize hG : t.basis g=G at tri a1 a2 a3 a4 a5 hu3
  generalize hdx : (p-1-X+(if G then k else 0))%p=dx at tri a1 a2 a3 a4 a5 hu3
  generalize hpar : decide (dx%2=1)=par at tri a1 a2 a3 a4 a5
  generalize hK : (dx/2+kConstant false par)%2^258=K at tri a1 a2 a3 a4 a5
  generalize hH : (K%2^257+delta par)%2^257=H at tri a1 a2 a3 a4 a5
  obtain ⟨lp,l1,l2,l3,l4,l5,l6,l7,l8⟩ := tri
  have dxlt : dx<p := by rw [←hdx]; exact Nat.mod_lt _ (by rw [p_val]; norm_num)
  have kh : ∀q∈hR w,q∉kR w := kR_hR w hn
  have kt : ∀q∈tR w,q∉kR w := kR_tR w hn
  have hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 dx u.basis := by
    constructor
    · change regValue (wireBlock w 0 258) u.basis=0
      rw [show wireBlock w 0 258=hR w from rfl,regValue_congr _ _ t.basis (fun q hq => hu2 q (kh q hq)),th0]
    · change regValue (wireBlock w 770 258) u.basis=dx
      exact hu3
    · change regValue (wireBlock w 1540 257) u.basis=0
      apply (regValue_zero _ _).mpr
      intro q hq
      rw [hu2 q (fun h' => List.disjoint_left.mp (blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)) h' hq)]
      exact hac q hq
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
    · change u.basis (w 1028)=false
      rw [hu2 _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact t1028
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec w hn dx dxlt u m' hin
  have e770 : u.basis (w 770)=par := by
    have sp := kR_split w hn u.basis
    rw [hu3] at sp
    rw [←hpar]
    cases hb : u.basis (w 770) <;> simp [hb] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  rw [hK] at zk
  have hv : 2*(dx/2+(if par then hConstant else 0))+(!par).toNat=2*H+(!par).toNat := by rw [a3]
  rw [hv] at zh
  apply State.extensionality
  · rw [lp,zp,hu]
  · funext q
    by_cases qh : q∈hR w
    · exact (regValue_eq_iff (hR w) _ _).mp (l1.trans zh.symm) q qh
    by_cases qk : q∈kR w
    · exact (regValue_eq_iff (kR w) _ _).mp (l2.trans zk.symm) q qk
    by_cases q1 : q=w 1028
    · rw [q1,l4,z1028]
    have nmut : q∉NativeFirstDirect.mutable w := by
      simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
      exact ⟨⟨fun h' => qh (blk_sub w 0 257 0 258 (by omega) (by omega) q h'),qk⟩,q1⟩
    rw [zrest q nmut,hu2 q qk]
    by_cases qt : q∈tR w
    · rw [(regValue_zero _ _).mp l3 q qt,(regValue_zero _ _).mp tt0 q qt]
    by_cases q4 : q=w 514
    · rw [q4,l5,t514]
    by_cases q5 : q=w 721
    · rw [q5,l6,t515]
    by_cases q6 : q=w 722
    · rw [q6,l7,t516]
    apply l8
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,qk⟩,qt⟩,q1,q4,q5,q6⟩

end Final


/-! ### Resources -/

def mSites (w : Nat → Wire) (g : Wire) : List Wire :=
  wireBlock w 0 515++wireBlock w 770 515++wireBlock w 1540 258++[w 721,w 722,g]

theorem in_mSites (w : Nat → Wire) (g : Wire) (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) : w i∈mSites w g := by
  simp only [mSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hi with h|h|h|h|h
  · exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩))
  · subst h; exact Or.inr (Or.inl rfl)
  · subst h; exact Or.inr (Or.inr (Or.inl rfl))

theorem blk_mSites (w : Nat → Wire) (g : Wire) (a n : Nat)
    (h : a + n ≤ 515 ∨ (770 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
    ∀q∈wireBlock w a n,q∈mSites w g := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact in_mSites w g i (by omega)

theorem g_mSites (w : Nat → Wire) (g : Wire) : g∈mSites w g := by simp [mSites]

theorem dBits_wires_sub (w : Nat → Wire) : ∀q∈mappedWires (dBits w),q=w 1028 := dBits_wire w

theorem lsub (w : Nat → Wire) (g : Wire) (l : List Wire) (h : ∀q∈l,q∈mSites w g) :
    l.toFinset⊆(mSites w g).toFinset := by
  intro q hq; exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem gate_sub (w : Nat → Wire) (g : Wire) (i : Instr) (h : ∀q∈i.wires,q∈mSites w g) :
    wires [i]⊆(mSites w g).toFinset := by
  intro q hq
  simp only [wires,Finset.union_empty] at hq
  exact List.mem_toFinset.mpr (h q hq)

theorem merged_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (merged w g k)⊆(mSites w g).toFinset := by
  have B := blk_mSites w g
  have I := in_mSites w g
  have G := g_mSites w g
  have mskH (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have mskS (v : Nat) : wires (maskedConstant g (srcR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset g (srcR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 0 256 (by omega) q hq))
  have notS : wires (notRegister (srcR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]; exact lsub w g _ (B 0 256 (by omega))
  have cmp : wires (compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514))⊆(mSites w g).toFinset := by
    rw [(compareLt_wires none (xR w) (srcR w) (cR w) (w 513) (w 514) (by simp [srcR,xR,wireBlock_length])
      (by simp [cR,srcR,xR,wireBlock_length])).1]
    apply lsub; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 513 (by omega)
    · exact B 770 256 (by omega) q hq
    · exact B 0 256 (by omega) q hq
    · exact B 256 256 (by omega) q hq
  have hC : wires (comparePart w g k)⊆(mSites w g).toFinset := by
    simp only [comparePart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨mskS _,cmp⟩,mskS _⟩
  have cx (a b : Nat) (ha : a < 515 ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have hP : wires (parGates w g k)⊆(mSites w g).toFinset := by
    unfold parGates
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hR' : wires (rotateRight (kR w))⊆(mSites w g).toFinset := by
    rw [(rotate_wires (kR w)).1]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub w g _ (B 770 258 (by omega))
  have hNot : wires (notRegister (kR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]
    exact lsub w g _ (B 770 258 (by omega))
  have hPr : wires (prodPart w g)⊆(mSites w g).toFinset := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub <;> intro q hq <;>
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hL : wires (loadK w g k)⊆(mSites w g).toFinset := by
    simp only [loadK,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub w g _ (B 0 258 (by omega)))
  have hK : wires (kAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hM1 : wires [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hM2 : wires [.measureX (w 721) [] [.CZ g (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl
    · exact I _ (by omega)
    · exact G
    · exact I _ (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mSites w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hH : wires (hAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · rw [dBits_wire w q hq]; exact I 1028 (by omega)
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mSites w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hT : wires (loadT w g k)⊆(mSites w g).toFinset := by
    simp only [loadT,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have hE : wires (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hHT : wires (hAddT w)⊆(mSites w g).toFinset := (hAddT_wires w).trans hH
  simp only [merged,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hC,⟨hP,hR'⟩,hNot⟩,hPr⟩,hL⟩,hK⟩,hL⟩,hM1⟩,hCp⟩,hHT⟩,hW⟩,hT⟩,hE⟩,hT⟩,hM2⟩


theorem merged_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (merged w g k)=1025 ∧ measurementCount (merged w g k)=1027 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := maskedConstant_counts c r v
  have x1 (r : List Wire) (v : Nat) := xorConstant_counts r v
  have n1 := notRegister_counts (kR w)
  have c1' := compareLt_counts none (xR w) (srcR w) (cR w) (w 513) (w 514)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,srcR,xR,wireBlock_length])
  have r1 := rotate_counts (kR w)
  have k1 := mappedAdd_counts (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length])
  have h1 := mappedAdd_counts (dBits w) (hpR w) (hC2 w) (w 1797)
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length])
  have e1 := eraseLtChain_counts (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length])
  have cp1 := copyRegister_counts none (wireBlock w 770 257) (hpR w) (by simp [hpR,wireBlock_length])
  have pg : toffoliCount (parGates w g k)=0 ∧ measurementCount (parGates w g k)=0 := by
    unfold parGates; split_ifs <;> simp [toffoliCount,measurementCount]
  have lx : (srcR w).length=256 := by simp [srcR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  rw [lx] at c1'
  rw [lk] at k1
  rw [lh] at h1
  rw [lt] at e1
  have hT := hAddT_counts w
  rw [hAddM,h1.1,h1.2] at hT
  have hT' : toffoliCount (hAddT w)=255 ∧ measurementCount (hAddT w)=256 := by omega
  simp only [merged,comparePart,prodPart,loadK,kAddM,hT'.1,hT'.2,loadT,toffoliCount_append,
    measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,n1.1,n1.2,c1'.1,c1'.2.1,
    r1.1,r1.2.1,k1.1,k1.2,h1.1,h1.2,e1.1,e1.2,cp1.1,cp1.2,pg.1,pg.2]
  simp [toffoliCount,measurementCount]

section Phys
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_physical (k : Nat) : GatePhysical (merged w g k) := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j := w_ne w hn i j hi hj h
  have gn (i : Nat) (hi : i<1798) : g≠w i := g_ne w hn g hg i hi
  have cxp (a b : Wire) (h : a≠b) : GatePhysical [.CX a b] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h]
  have ccxp (a b c : Wire) (h1 : a≠c) (h2 : b≠c) : GatePhysical [.CCX a b c] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h1,h2]
  have mp (c : Wire) (c' : Wire) : GatePhysical [.measureX c [] [.CZ c' c]] ∧
      GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by
    simp [GatePhysical,PhysicalInstr]
  have gS : g∉srcR w := g_out w hn g hg 0 256 (by omega)
  have gH : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have cmpP : GatePhysical (compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514)) := by
    apply compareLt_physical
    · have a1 := blk_dis w hn 770 256 0 256 (by omega) (by omega) (by omega)
      have a2 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
      have a3 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
      have l1 : (xR w++srcR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 770 256 (by omega),src_nd w hn,a1⟩
      have l2 : (xR w++srcR w++cR w).Nodup := by
        apply List.nodup_append'.mpr
        refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
        apply List.disjoint_left.mpr
        intro q hq hc'
        rcases List.mem_append.mp hq with h1|h1
        · exact List.disjoint_left.mp a2 h1 hc'
        · exact List.disjoint_left.mp a3 h1 hc'
      simp only [List.cons_append,List.append_assoc] at l2 ⊢
      refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,by simpa [List.append_assoc] using l2⟩⟩
      · simp only [List.mem_cons,List.mem_append,not_or]
        exact ⟨ne 514 513 (by omega) (by omega) (by omega),nb w hn 514 770 256 (by omega) (by omega) (by omega),
          nb w hn 514 0 256 (by omega) (by omega) (by omega),nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
      · simp only [List.mem_append,not_or]
        exact ⟨nb w hn 513 770 256 (by omega) (by omega) (by omega),nb w hn 513 0 256 (by omega) (by omega) (by omega),
          nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
    · simp
  have kP : GatePhysical (kAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      refine ⟨?_,?_,?_⟩
      · intro e; exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq')
      · exact fun h' => hR_kR w hn _ h' hq'
      · exact fun h' => List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq' h'
  have hP : GatePhysical (hAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      have : q∈mappedWires (dBits w) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
      rw [dBits_wire w q this,List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne 1028 1797 (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
        nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have eP : GatePhysical (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)) := by
    apply eraseLtChain_physical
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    rw [List.cons_append,List.cons_append]
    refine List.nodup_cons.mpr ⟨?_,l2⟩
    simp only [List.mem_append,not_or]
    exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cpP : GatePhysical (copyRegister none (wireBlock w 770 257) (hpR w)) :=
    copyRegister_physical none _ _ (List.nodup_append'.mpr ⟨blk_nd w hn 770 257 (by omega),
      blk_nd w hn 1 257 (by omega),blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩) (by simp)
  have parP : GatePhysical (parGates w g k) := by
    unfold parGates
    split_ifs <;> simp only [gatePhysical_append] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first
        | exact cxp _ _ (ne _ _ (by omega) (by omega) (by omega))
        | exact cxp _ _ (gn _ (by omega))
        | simp [GatePhysical]
  have rotP := (rotate_physical (kR w) (kR_nd w hn)).1
  have prodP : GatePhysical (prodPart w g) := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,gatePhysical_append]
    exact ⟨ccxp _ _ _ (gn _ (by omega)) (ne _ _ (by omega) (by omega) (by omega)),
      ccxp _ _ _ (ne _ _ (by omega) (by omega) (by omega)) (ne _ _ (by omega) (by omega) (by omega))⟩
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h1286 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h1287 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t1286 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  have lkP : GatePhysical (loadK w g k) := by
    simp only [loadK,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨xorConstant_physical _ _,maskedConstant_physical _ _ _ gH⟩,maskedConstant_physical _ _ _ h514⟩,
      maskedConstant_physical _ _ _ h1028⟩,maskedConstant_physical _ _ _ h1286⟩,maskedConstant_physical _ _ _ h1287⟩
  have ltP : GatePhysical (loadT w g k) := by
    simp only [loadT,gatePhysical_append]
    exact ⟨maskedConstant_physical _ _ _ gT,maskedConstant_physical _ _ _ t1286⟩
  have w0P : GatePhysical [.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,ne 1028 0 (by omega) (by omega) (by omega)]
  have cP : GatePhysical (comparePart w g k) := by
    simp only [comparePart,gatePhysical_append]
    exact ⟨⟨maskedConstant_physical _ _ _ gS,cmpP⟩,maskedConstant_physical _ _ _ gS⟩
  have m1 : GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have m2 : GatePhysical [.measureX (w 721) [] [.CZ g (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have hPT : GatePhysical (hAddT w) := hAddT_physical w hP
  simp only [merged,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cP,⟨parP,rotP⟩,notRegister_physical _⟩,prodP⟩,lkP⟩,kP⟩,lkP⟩,m1⟩,cpP⟩,hPT⟩,w0P⟩,ltP⟩,eP⟩,ltP⟩,m2⟩

end Phys

theorem gs1 (i : Instr) : Challenge.gateSlots [i]=Challenge.instructionSlots i := by
  simp [Challenge.gateSlots]

theorem merged_slots (w : Nat → Wire) (g : Wire) (k : Nat) : Challenge.gateSlots (merged w g k)≤25000 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := Baselines.maskedConstant_gateSlots_le c r v
  have x1 (r : List Wire) (v : Nat) := Baselines.xorConstant_gateSlots_le r v
  have c1' := Baselines.compareLt_gateSlots_le none (xR w) (srcR w) (cR w) (w 513) (w 514)
  have r1 := (Baselines.rotate_gateSlots_le (kR w)).1
  have k1 := Baselines.mappedAdd_gateSlots_le (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
  have h1 := Baselines.mappedAdd_gateSlots_le (dBits w) (hpR w) (hC2 w) (w 1797)
  have e1 := Baselines.eraseLt_gateSlots_le (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
  have pg : Challenge.gateSlots (parGates w g k)≤6 := by
    unfold parGates; split_ifs <;> simp [Challenge.gateSlots,Challenge.instructionSlots]
  have pr : Challenge.gateSlots (prodPart w g)=2 := by simp [prodPart,Challenge.gateSlots,Challenge.instructionSlots]
  have w0 : Challenge.gateSlots [.CX (w 1028) (w 0),.X (w 0)]=2 := by simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q1 : Challenge.gateSlots [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q2 : Challenge.gateSlots [.measureX (w 721) [] [.CZ g (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have lK : Challenge.gateSlots (loadK w g k)≤6*258 := by
    simp only [loadK,Challenge.gateSlots_append]
    have := x1 (hR w) (c1 k); have := m1 g (hR w) (cg k); have := m1 (w 514) (hR w) (cf k)
    have := m1 (w 1028) (hR w) (cp k); have := m1 (w 721) (hR w) (cgp k); have := m1 (w 722) (hR w) (cfp k)
    simp only [hR,wireBlock_length] at *
    omega
  have lT : Challenge.gateSlots (loadT w g k)≤2*256 := by
    simp only [loadT,Challenge.gateSlots_append]
    have := m1 g (tR w) (thrA k); have := m1 (w 721) (tR w) (thrB k)
    simp only [tR,wireBlock_length] at *
    omega
  have cP : Challenge.gateSlots (comparePart w g k)≤2*256+12*256+4 := by
    simp only [comparePart,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
    have := m1 g (srcR w) k
    simp only [srcR,xR,wireBlock_length] at *
    omega
  have cp : Challenge.gateSlots (copyRegister none (wireBlock w 770 257) (hpR w))=257 := by
    simp [hpR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hp8 w).length=256 := by simp [hp8,wireBlock_length]
  have lhR : (hR w).length=258 := by simp [hR,wireBlock_length]
  rw [lk] at r1
  rw [mappedRead_length,lhR] at k1
  rw [dBits_length] at h1
  rw [lh] at e1
  have nk : Challenge.gateSlots (notRegister (kR w))=258 := by
    simp [Baselines.notRegister_gateSlots,kR,wireBlock_length]
  have hS := hAddT_slots w
  rw [hAddM] at hS
  simp only [merged,Challenge.gateSlots_append,pr,w0,q1,q2,cp,kAddM,nk]
  omega

end ECDSAAdd.Entrant.E1Reflected

end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.E1ReflectedPlacement =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.E1QubitPlacement
-- consolidated import: import ECDSAAdd.Submission.Entrant.E1Reflected

/-! Full all-record physical transfer for the reflected-input merged entry.
Research source, NOT elaborated here. The r-state relation is the internal
boundary supplied by the removed square output reflection, not a new external
point-addition premise. All clean scratch values are derived from dialogPool0.
-/
namespace ECDSAAdd.Entrant.E1ReflectedPlacement
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement

def entryR (L : ControlledPointLayout) (k : Fp) : Program :=
  renameProgram (pmapR L) (E1Reflected.merged base (base 2400) k.val)

theorem mergedR_S (k : Nat) : wires (E1Reflected.merged base (base 2400) k)⊆S :=
  E1Reflected.merged_support base (base 2400) k

section Entry
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem entryR_eq (k : Fp) (s r : State) (X : Nat) (hX : X<p) (G : Bool)
    (hx : regValue L.point.x s.basis=X) (hg : s.basis L.core.generic=G)
    (hc : regValue L.dialogPool s.basis=0)
    (rphase : r.phase=s.phase)
    (rx : regValue L.point.x r.basis=p-1-X)
    (rout : ∀q,q∉L.point.x → r.basis q=s.basis q) (m1 m2 : List Bool) :
    run (entryR L k) m1 s=run (fastConstAdd L L.point.x k++E1QubitPlacement.tickF L) m2 r := by
  have inj := pmap_inj L hw hn
  have pool := pmap_pool L hw hn
  have hzero := (regValue_zero _ _).mp hc
  let F := pmapR L
  let t : State := pullState F s
  have clean (q : Wire) (hq : q∈S) (h1 : q∉wireBlock base 770 256) (h2 : q≠base 2400) :
      t.basis q=false := hzero _ (pool q hq h1 h2)
  have inS (i : Nat) (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      base i∈S := List.mem_toFinset.mpr (E1Reflected.in_mSites base (base 2400) i hi)
  have notx (i : Nat) (hi : ¬ (770 ≤ i ∧ i < 1026)) : base i∉wireBlock base 770 256 := by
    intro h; obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj; have := base_injective e; omega
  have ne2400 (i : Nat) (hi : i≠2400) : base i≠base 2400 := fun e => hi (base_injective e)
  have cl (i : Nat) (hi : i < 515 ∨ (1026 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) :
      t.basis (base i)=false :=
    clean _ (inS i (by omega)) (notx i (by omega)) (ne2400 i (by omega))
  have blkz (a n : Nat) (h : a + n ≤ 515 ∨ (1026 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
      regValue (wireBlock base a n) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact cl i (by omega)
  have xval : regValue (wireBlock base 770 256) t.basis=X := by
    change regValue (wireBlock base 770 256) (fun q => s.basis (F q))=X
    rw [regValue_pull,pmap_x L hw hn,hx]
  have tk0 : regValue (E1Reflected.kR base) t.basis=X := by
    rw [E1Reflected.kR_x base base_pool_nodup,show E1Reflected.xR base=wireBlock base 770 256 from rfl,xval,
      blkz 1026 2 (by omega)]
    simp
  have tg : t.basis (base 2400)=G := by
    change s.basis (pmapR L (base 2400))=G
    rw [pmap_g L hw hn,hg]
  -- The reflected comparison state differs only on x; no new scratch premise.
  have gx : L.core.generic∉L.point.x := ((E1QubitPlacement.lay L hw hn _).2.2 rfl).1
  have px (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x :=
    ((E1QubitPlacement.lay L hw hn q).2.1 hq).1
  have rg : r.basis L.core.generic=G := (rout _ gx).trans hg
  have rc : regValue L.dialogPool r.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq => rout q (px q hq)),hc]
  have xrlt : p-1-X<p := by
    rw [E1Reflected.p_val] at hX ⊢
    omega
  have fca := fastConstAdd_correct L hw hn L.point.x (Or.inl rfl) k (p-1-X) G xrlt r
    (m2.take (measurementCount (fastConstAdd L L.point.x k))) rg rx rc
  generalize hs1 : run (fastConstAdd L L.point.x k) (m2.take (measurementCount (fastConstAdd L L.point.x k))) r=s1 at fca
  obtain ⟨p1r,x1,o1r⟩ := fca
  have p1 : s1.phase=s.phase := p1r.trans rphase
  have o1 (q : Wire) (hq : q∉L.point.x) : s1.basis q=s.basis q := (o1r q hq).trans (rout q hq)
  let u : State := ⟨t.phase,fun q => if q∈E1Reflected.kR base then s1.basis (F q) else t.basis q⟩
  have hu2 : ∀q,q∉E1Reflected.kR base → u.basis q=t.basis q := by
    intro q hq; simp [u,hq]
  have xS : ∀q∈L.point.x,∃a∈S,F a=q ∧ a∈wireBlock base 770 256 := by
    intro q hq
    rw [←pmap_x L hw hn] at hq
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    refine ⟨a,?_,rfl,ha⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_range'_1] at hi
    exact inS i (by omega)
  have hu3 : regValue (E1Reflected.kR base) u.basis=(p-1-X+(if t.basis (base 2400) then k.val else 0))%p := by
    rw [tg,E1Reflected.kR_x base base_pool_nodup]
    have e1 : regValue (E1Reflected.xR base) u.basis=regValue L.point.x s1.basis := by
      rw [←pmap_x L hw hn,←regValue_pull]
      apply regValue_congr
      intro q hq
      have : q∈E1Reflected.kR base := E1Reflected.blk_sub base 770 256 770 258 (by omega) (by omega) q hq
      simp only [u,this,if_true]
      rfl
    have e2 : regValue (wireBlock base 1026 2) u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      have kq : base i∈E1Reflected.kR base := E1Reflected.blk_sub base 1026 2 770 258 (by omega) (by omega) _ hq
      have outx : F (base i)∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha (base i) (inS i (by omega)) ea
        subst this
        exact notx i (by omega) ax
      simp only [u,kq,if_true]
      rw [o1 _ outx]
      exact cl i (by omega)
    rw [e1,e2,x1]; simp
  have t1 := (regValue_zero _ _).mp (blkz 0 258 (by omega))
  have eqL := E1Reflected.merged_eq_forward base (base 2400) base_pool_nodup g2400 k.val k.isLt X hX t u m1
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) tk0 (blkz 0 258 (by omega))
    (blkz 1029 256 (by omega)) (cl 1028 (by omega)) (cl 514 (by omega)) (cl 721 (by omega)) (cl 722 (by omega))
    (fun i h1 h2 => cl i (by omega)) (cl 513 (by omega))
    (fun q hq => by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hi
      exact cl i (by omega)) (cl 1797 (by omega)) rfl hu2 hu3
  -- transport both sides
  have hS : ∀q∈S,t.basis q=s.basis (F q) := fun q _ => rfl
  have newSide := run_rename_pool F S inj _ (mergedR_S k.val) m1 t s rfl hS
  have uS : ∀q∈S,u.basis q=s1.basis (F q) := by
    intro q hq
    by_cases kq : q∈E1Reflected.kR base
    · simp [u,kq]
    · simp only [u,kq,if_false]
      change s.basis (F q)=s1.basis (F q)
      have outx : F q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,ax⟩ := xS _ hm
        have := inj a ha q hq ea
        subst this
        exact kq (E1Reflected.blk_sub base 770 256 770 258 (by omega) (by omega) _ ax)
      rw [o1 _ outx]
  have oldSide := run_rename_pool F S inj _ forward_S
    (m2.drop (measurementCount (fastConstAdd L L.point.x k))) u s1 (by simp [u,t,pullState,p1]) uS
  have rhs : run (fastConstAdd L L.point.x k++E1QubitPlacement.tickF L) m2 r=
      run (E1QubitPlacement.tickF L) (m2.drop (measurementCount (fastConstAdd L L.point.x k))) s1 := by
    rw [run_append,hs1]
  rw [rhs]
  apply State.extensionality
  · rw [entryR,newSide.1,eqL,E1QubitPlacement.tickF,oldSide.1]
  · funext q
    by_cases im : q∈S.image F
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp im
      rw [entryR,newSide.2 a ha,eqL,E1QubitPlacement.tickF,oldSide.2 a ha]
    · rw [entryR,run_rename_pool_outside F S _ (mergedR_S k.val) m1 s q im,E1QubitPlacement.tickF,
        run_rename_pool_outside F S _ forward_S _ s1 q im]
      have outx : q∉L.point.x := by
        intro hm
        obtain ⟨a,ha,ea,_⟩ := xS _ hm
        exact im (Finset.mem_image.mpr ⟨a,ha,ea⟩)
      rw [o1 q outx]

end Entry

open Challenge
attribute [local irreducible] wires

theorem entryR_counts (L : ControlledPointLayout) (k : Fp) :
    toffoliCount (entryR L k)=1025 ∧ measurementCount (entryR L k)=1027 := by
  have r := renameProgram_counts (pmapR L) (E1Reflected.merged base (base 2400) k.val)
  have c := E1Reflected.merged_counts base (base 2400) k.val
  rw [entryR,r.1,r.2]; exact c

theorem entryR_slots (L : ControlledPointLayout) (k : Fp) : gateSlots (entryR L k)≤25000 := by
  simpa only [entryR,Baselines.rename_gateSlots] using
    E1Reflected.merged_slots base (base 2400) k.val

theorem entryR_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (k : Fp) : GatePhysical (entryR L k) := by
  rw [entryR]
  exact gatePhysical_rename_support (pmapR L) (E1Reflected.merged base (base 2400) k.val)
    (fun a ha b hb e => pmap_inj L hw hn a (mergedR_S k.val ha) b (mergedR_S k.val hb) e)
    (E1Reflected.merged_physical base (base 2400) base_pool_nodup g2400 k.val)

theorem entryR_sites (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (entryR L k)⊆(OB5Support.sites L).toFinset := by
  have hlog : wires (renameProgram sig (renameProgram rho
      (E1Reflected.merged base (base 2400) k.val)))⊆OB5Support.logicalSites := by
    intro q hq
    simp only [renameProgram_support,Finset.mem_image] at hq
    obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩ := hq
    obtain ⟨j,rfl,hj⟩ := S_cases b (mergedR_S k.val hb)
    rw [rho_base,sig_base]
    exact sw_logical _ (rhoN_range j hj)
  have h := OB5Support.placed_support_logical L hw _ hlog
  simpa only [entryR,renameProgram_comp,pmapR,pmap,Function.comp_def] using h

/-- Both the ordinary and reflected E1 programs have the same support envelope. -/
theorem logicalR_omits (k i : Nat)
    (hi : i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719]) :
    base i∉wires (renameProgram sig (renameProgram rho
      (E1Reflected.merged base (base 2400) k))) := by
  intro h
  simp only [renameProgram_support,Finset.mem_image] at h
  obtain ⟨a,⟨b,hb,rfl⟩,eq⟩ := h
  obtain ⟨j,rfl,hj⟩ := S_cases b (mergedR_S k hb)
  rw [rho_base,sig_base] at eq
  have e := base_injective eq
  exact sw_avoid j hj (e.symm ▸ hi)

end ECDSAAdd.Entrant.E1ReflectedPlacement
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Entry =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588BFFinal
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Square
-- consolidated import: import ECDSAAdd.Submission.Entrant.E1ReflectedPlacement

/-! Both merged entries retain the complete rolling inverse phases. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires

def tailP (a : Bool) : Program := Rolling1588.stackForward a++skywalkArithmeticClear base

def restE (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (tailP true)++
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))

def restX (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (tailP false)++
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))

def entryStage (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky++E1QubitPlacement.entryM L kx++restE L

def squareEntry (L : ControlledPointLayout) (k : Fp) : Program :=
  ReflectionE1Square.program L++E1ReflectedPlacement.entryR L k

def secondStage (L : ControlledPointLayout) (k cy : Fp) : Program :=
  squareEntry L k++restX L++exitY L cy

theorem entry_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry Rolling1588.entryKernel L=E1QubitPlacement.tickF L++restE L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,Rolling1588.entryKernel,Rolling1588.firstPhase,restE,tailP,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem exit_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.exit Rolling1588.exitKernel L=E1QubitPlacement.tickF L++restX L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,Rolling1588.exitKernel,Rolling1588.firstPhase,restX,tailP,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem entryStage_step (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStage L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  have add:=fastStep_addX L hw hn X Y G origin kx
  have divide:=division_step Rolling1588.entryKernel Rolling1588.entryKernel_support
    Rolling1588.entry_correct L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior:=add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky++E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx++fusedY L ky++E1QubitPlacement.tickF L)
    (R:=restE L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryStage,division,entry_split,List.append_assoc] using prior

/-- The deleted reflection and changed entry use independent record lists.
The equality ends before the common suffix, so no suffix tape equality is assumed. -/
theorem squareEntry_eq (k : Fp) (X Y : Fp) (G : Bool) (origin : BasisState)
    (s : State) (m1 m2 : List Bool) (v : PointDialogValues L X Y G origin s.basis) :
    run (squareEntry L k) m1 s=
      run (SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++
        E1QubitPlacement.tickF L) m2 s := by
  let n1:=measurementCount (ReflectionE1Square.program L)
  let n2:=measurementCount (SquareCarryLoan719BF.program L)
  obtain ⟨a,ha⟩ : ∃a : State,run (ReflectionE1Square.program L) (m1.take n1) s=a := ⟨_,rfl⟩
  obtain ⟨r,hr⟩ : ∃r : State,run (SquareCarryLoan719BF.program L) (m2.take n2) s=r := ⟨_,rfl⟩
  have fresh:=ReflectionE1Square.boundary L hw hn X Y G origin s (m1.take n1) v
  have prior:=SquareCarryLoan719BF.step L hw hn X Y G origin s (m2.take n2) v
  rw [ha] at fresh
  rw [hr] at prior
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  let R:=p-1-Z.val
  have ppos : 0<p := by norm_num [p]
  have rp : R<p := by
    change p-1-Z.val<p
    omega
  have ax : regValue L.point.x a.basis=R:=fresh.2.1
  have ag : a.basis L.core.generic=G :=
    (fresh.2.2 _ (((E1QubitPlacement.lay L hw hn _).2.2 rfl).1)).trans v.generic
  have ac : regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ s.basis
      (fun q hq=>fresh.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).1)),v.clean]
  have involution (n : Nat) (bound : n<p) : n=p-1-(p-1-n) := by omega
  have rx : regValue L.point.x r.basis=p-1-R := by
    have value : regValue L.point.x r.basis=Z.val:=prior.2.x
    exact value.trans (involution Z.val Z.isLt)
  have outside (q : Wire) (hq : q∉L.point.x) : r.basis q=a.basis q := by
    have oldFrame : r.basis q=s.basis q := by
      by_cases hy : q∈L.point.y
      · exact (regValue_eq_iff _ _ _).mp (prior.2.y.trans v.y.symm) q hy
      · have away : q∉L.point.x++L.point.y:=by simp only [List.mem_append,not_or];exact ⟨hq,hy⟩
        exact (prior.2.rest q away).trans (v.rest q away).symm
    exact oldFrame.trans (fresh.2.2 q hq).symm
  have eq:=E1ReflectedPlacement.entryR_eq L hw hn k a r R rp G ax ag ac
    (prior.1.trans fresh.1.symm) rx outside (m1.drop n1) (m2.drop n2)
  simpa only [squareEntry,run_append,n1,n2,ha,hr,List.append_assoc] using eq

theorem secondStage_step (X Y k cy : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStage L k cy)
      (PointDialogValues L Z (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=fusedMultiply_step L hw hn (FrontierEntry1591Callers.exit Rolling1588.exitKernel L)
    (exit_correct Rolling1588.exitKernel Rolling1588.exitKernel_support Rolling1588.exit_correct L hw hn)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStage,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=restX L++exitY L cy)
  · intro s v m1 m2
    exact squareEntry_eq L hw hn k X Y G origin s m1 m2 v
  · simpa only [secondStage,fusedMultiply,exit_split,List.append_assoc,Z] using prior

end Correct
end ECDSAAdd.Entrant.ReflectionE1
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Generic =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Entry

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5
  EntryFuse EntryFuseFinite ExitFusionResearch
attribute [local irreducible] run wires

def correction (cx : Fp) : Fp := 3*cx-(SquareCarryLoan719BF.K:Nat)

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStage L (-cx) (-cy)++secondStage L (correction cx) cy++fastConstNeg L cx

def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clrF L++renameProgram (swapF L) (generic L cx cy)++clrF L

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  zrep L++mid L cx cy++zrep L

theorem gen_shape (L : ControlledPointLayout) (cx cy : Fp) :
    gen L cx cy=GenericQ5Geometry.wrapG L (generic L cx cy) := rfl

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStage_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold correction
    ring
  have second:=secondStage_step L hw hn (X-cx) a (correction cx) cy true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  have finish:=fastStep_negX L hw hn d (a*d-cy) true origin cx
  simp only [if_true] at finish
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at finish
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at second finish
  exact (first.seq second).seq finish

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStage_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStage_step L hw hn X (Y/X) (correction cx) cy false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have finish:=fastStep_negX L hw hn X Y false origin cx
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second finish
  rw [back] at second
  exact (first.seq second).seq finish


theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (X.val ≠ 5) = fin) (h2 : decide (X'.val ≠ 5) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clrF_step L hw hn X Y G base
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
        L.point.finite ^^ decide (X'.val ≠ 5)) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := zrep_step L hw hn 0 5 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    have mid := midFFused_values L hw hn cx cy 5 0 5 0 false s.basis false
      (fun base' => generic_false L hw hn 5 0 cx cy base' finFive_ne_zero) hfin
      (by simp [finFive_val]) (by simp [finFive_val])
    have z2 := zrep_step L hw hn 5 0 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (x.val ≠ 5) = true := decide_eq_true (val_ne_five hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide ((genericX x y cx cy).val ≠ 5) = true :=
        decide_eq_true (val_ne_five (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end Correct
end ECDSAAdd.Entrant.ReflectionE1
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Resources =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Generic

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] wires toffoliCount measurementCount gateSlots

abbrev baselineGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ControlLoan1589BFFinal.Offset.generic L (division Rolling1588.entryKernel L)
    (SquareCarryLoan719BF.program L) (FrontierEntry1591Callers.exit Rolling1588.exitKernel L) cx cy

private theorem envelopes_of_shapes (A0 Y T E S R A1 X EY N M RF New Old : Program)
    (newShape : New=(Y++M++E)++(S++RF++X++EY)++N)
    (oldShape : Old=A0++(Y++(T++E))++(S++R)++A1++(T++X)++EY++N) :
    New⊆Old++M++RF ∧ wires New⊆wires Old∪wires M∪wires RF := by
  rw [newShape,oldShape]
  constructor
  · intro i hi
    simp only [List.mem_append] at hi ⊢
    tauto
  · intro q hq
    simp only [wires_append,Finset.mem_union] at hq ⊢
    tauto

private theorem envelopes (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy⊆baselineGeneric L cx cy++E1QubitPlacement.entryM L (-cx)++
      E1ReflectedPlacement.entryR L (correction cx) ∧
    wires (generic L cx cy)⊆wires (baselineGeneric L cx cy)∪
      wires (E1QubitPlacement.entryM L (-cx))∪
        wires (E1ReflectedPlacement.entryR L (correction cx)) := by
  apply envelopes_of_shapes
    (fastConstAdd L L.point.x (-cx)) (fusedY L (-cy)) (E1QubitPlacement.tickF L)
    (restE L) (ReflectionE1Square.program L) (ReflectionE1Square.reflectedTail L)
    (fastConstAdd L L.point.x (3*cx-(ControlLoan1589BFFinal.Offset.K:Nat)))
    (restX L) (exitY L cy) (fastConstNeg L cx) (E1QubitPlacement.entryM L (-cx))
    (E1ReflectedPlacement.entryR L (correction cx))
  · rfl
  · simp only [baselineGeneric,ControlLoan1589BFFinal.Offset.generic,division,
      entry_split,exit_split,ReflectionE1Square.program_split]

theorem instructions_subset (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy⊆baselineGeneric L cx cy++E1QubitPlacement.entryM L (-cx)++
      E1ReflectedPlacement.entryR L (correction cx) :=
  (envelopes L cx cy).1

theorem support_envelope (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic L cx cy)⊆wires (baselineGeneric L cx cy)∪
      wires (E1QubitPlacement.entryM L (-cx))∪
        wires (E1ReflectedPlacement.entryR L (correction cx)) :=
  (envelopes L cx cy).2

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
  (support_envelope L cx cy).trans (Finset.union_subset
    (Finset.union_subset (Rolling1588BFFinal.generic_support L hw hn cx cy)
      (E1QubitPlacement.entryM_sites L hw (-cx)))
    (E1ReflectedPlacement.entryR_sites L hw (correction cx)))

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have old:=ControlLoan1589BFFinal.Offset.generic_physical L hw hn
    (division Rolling1588.entryKernel L) (SquareCarryLoan719BF.program L)
    (FrontierEntry1591Callers.exit Rolling1588.exitKernel L)
    (division_physical Rolling1588.entryKernel Rolling1588.entryKernel_support
      Rolling1588.entryKernel_physical L hw hn)
    (SquareCarryLoan719BF.physical L hw hn)
    (placed_physical Rolling1588.exitKernel Rolling1588.exitKernel_support
      Rolling1588.exitKernel_physical L hw hn) cx cy
  have full : GatePhysical (baselineGeneric L cx cy++E1QubitPlacement.entryM L (-cx)++
      E1ReflectedPlacement.entryR L (correction cx)) := by
    rw [gatePhysical_append,gatePhysical_append]
    exact ⟨⟨old,E1QubitPlacement.entryM_physical L hw hn (-cx)⟩,
      E1ReflectedPlacement.entryR_physical L hw hn (correction cx)⟩
  intro i hi
  exact full i (instructions_subset L cx cy hi)

private def logicalTarget (i : Nat) : Nat :=
  if i=1800 then 2312 else if i=770 then 1026 else if i=1285 then 1541 else
    if i=1286 then 1542 else if i=769 then 1797 else i

private theorem target_facts (L : ControlledPointLayout) (i : Nat)
    (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    wireFn2 L (base (logicalTarget i))=L.core.poolWire i ∧
    base (logicalTarget i)∈OB5Support.logicalSites ∧
    logicalTarget i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719] := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals refine ⟨rfl,?_,by decide⟩
  all_goals
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨_,?_,rfl⟩
    simp only [logicalTarget,OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    norm_num

private theorem placed_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (P : Program) (support : wires P⊆OB5Support.logicalSites) (i : Nat)
    (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719])
    (free : base (logicalTarget i)∉wires P) :
    L.core.poolWire i∉wires (renameProgram (wireFn2 L) P) := by
  obtain ⟨map,logical,_⟩:=target_facts L i hi
  rw [renameProgram_support]
  intro used
  obtain ⟨q,hq,eq⟩:=Finset.mem_image.mp used
  have same : wireFn2 L q=wireFn2 L (base (logicalTarget i)):=eq.trans map.symm
  have back:=(placement2 L hw hn).injectiveOnSlots q
    (ArithmeticOB5.logical_sub_old (support hq)) (base (logicalTarget i))
    (ArithmeticOB5.logical_sub_old logical) same
  exact free (back ▸ hq)

private theorem entry_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (E1QubitPlacement.entryM L k) := by
  rw [E1QubitPlacement.entryM_eq]
  exact placed_free L hw hn _ (E1QubitPlacement.logicalM k.val) i hi
    (E1QubitPlacement.merged_omits k.val _ (target_facts L i hi).2.2)

private theorem reflected_logical (k : Nat) :
    wires (renameProgram E1QubitPlacement.sig (renameProgram E1QubitPlacement.rho
      (E1Reflected.merged base (base 2400) k)))⊆OB5Support.logicalSites := by
  intro q hq
  simp only [renameProgram_support,Finset.mem_image] at hq
  obtain ⟨a,⟨b,hb,rfl⟩,rfl⟩:=hq
  obtain ⟨j,rfl,hj⟩:=E1QubitPlacement.S_cases b (E1ReflectedPlacement.mergedR_S k hb)
  rw [E1QubitPlacement.rho_base,E1QubitPlacement.sig_base]
  exact E1QubitPlacement.sw_logical _ (E1QubitPlacement.rhoN_range j hj)

private theorem reflected_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (E1ReflectedPlacement.entryR L k) := by
  have h:=placed_free L hw hn _ (reflected_logical k.val) i hi
    (E1ReflectedPlacement.logicalR_omits k.val _ (target_facts L i hi).2.2)
  simpa only [E1ReflectedPlacement.entryR,renameProgram_comp,E1QubitPlacement.pmapR,
    E1QubitPlacement.pmap,Function.comp_def] using h

private theorem kernel_free (entrySide : Bool) (i : Nat)
    (hi : i∈[2312,766,765,767,1026,1541,1542,1797,768,718,719]) :
    base i∉wires (if entrySide then Rolling1588.entryKernel else Rolling1588.exitKernel) := by
  by_cases a : i=768
  · subst i;cases entrySide
    · exact Rolling1588.exitKernel_768_free
    · exact Rolling1588.entryKernel_768_free
  by_cases b : i=718
  · subst i;cases entrySide
    · exact Rolling1588.exitKernel_718_free
    · exact Rolling1588.entryKernel_718_free
  by_cases c : i=719
  · subst i;cases entrySide
    · exact Rolling1588.exitKernel_719_free
    · exact Rolling1588.entryKernel_719_free
  have old : i∈logicalOmissions := by
    simp only [logicalOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
  cases entrySide
  · exact Rolling1588.exitKernel_free i old
  · exact Rolling1588.entryKernel_free i old

theorem baseline_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (baselineGeneric L cx cy) := by
  have bounds : 515≤ i ∧ i<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega
  have en:=placed_free L hw hn _ Rolling1588.entryKernel_support i hi
    (kernel_free true _ (target_facts L i hi).2.2)
  have ex:=placed_free L hw hn _ Rolling1588.exitKernel_support i hi
    (kernel_free false _ (target_facts L i hi).2.2)
  have sq : L.core.poolWire i∉wires (SquareCarryLoan719BF.program L) := by
    by_cases h : i=719
    · subst i;exact SquareCarryLoan719BF.retired_free719 L hw hn
    · apply SquareCarryLoan719BF.square_free L hw hn i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;tauto
  apply ControlLoan1589BFFinal.Offset.generic_free L hw hn
    (division Rolling1588.entryKernel L) (SquareCarryLoan719BF.program L)
    (FrontierEntry1591Callers.exit Rolling1588.exitKernel L) i bounds _ sq ex cx cy
  intro k
  have constant:=ExitGenericQ5.constant_ports_avoid_large L hw hn i bounds L.point.y (Or.inr rfl)
  simp only [division,FrontierEntry1591Callers.entry,wires_append,Finset.mem_union,not_or]
  exact ⟨fun used=>constant (fusedY_support L hw k used),en⟩

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (generic L cx cy) := by
  intro used
  have member:=support_envelope L cx cy used
  simp only [Finset.mem_union] at member
  rcases member with (old|ordinary)|reflected
  · exact baseline_free L hw hn cx cy i hi old
  · exact entry_free L hw hn (-cx) i hi ordinary
  · exact reflected_free L hw hn (correction cx) i hi reflected

theorem generic_counts_delta (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (generic L cx cy)+753=toffoliCount (baselineGeneric L cx cy) ∧
    measurementCount (generic L cx cy)+751=measurementCount (baselineGeneric L cx cy) := by
  have first:=E1QubitPlacement.prefix_counts L hw (-cx)
  have second:=E1QubitPlacement.prefix_counts L hw (correction cx)
  have ordinary:=E1QubitPlacement.entryM_counts L (correction cx)
  have reflected:=E1ReflectedPlacement.entryR_counts L (correction cx)
  have square:=ReflectionE1Square.counts_delta L hw
  simp only [generic,entryStage,secondStage,squareEntry,baselineGeneric,
    ControlLoan1589BFFinal.Offset.generic,division,entry_split,exit_split,
    toffoliCount_append,measurementCount_append,correction,SquareCarryLoan719BF.K,
    ControlLoan1589BFFinal.Offset.K,ControlLoan1589BFSquare.K] at first second ordinary reflected square ⊢
  constructor <;> omega

theorem generic_slots_delta (L : ControlledPointLayout) (cx cy : Fp) :
    gateSlots (generic L cx cy)≤ gateSlots (baselineGeneric L cx cy)+50000 := by
  have first:=E1QubitPlacement.entryM_slots L (-cx)
  have second:=E1ReflectedPlacement.entryR_slots L (correction cx)
  simp only [generic,entryStage,secondStage,squareEntry,baselineGeneric,
    ControlLoan1589BFFinal.Offset.generic,division,entry_split,exit_split,
    ReflectionE1Square.program_split,gateSlots_append]
  omega

private theorem baseline_gen_shape (L : ControlledPointLayout) (cx cy : Fp) :
    Rolling1588BFFinal.gen L cx cy=GenericQ5Geometry.wrapG L (baselineGeneric L cx cy) := by
  simp only [Rolling1588BFFinal.gen,ControlLoan1589BFFinal.Offset.gen_shape,baselineGeneric]

private theorem wrap_counts_delta (L : ControlledPointLayout) (A B : Program)
    (h : toffoliCount A+753=toffoliCount B ∧ measurementCount A+751=measurementCount B) :
    toffoliCount (GenericQ5Geometry.wrapG L A)+753=toffoliCount (GenericQ5Geometry.wrapG L B) ∧
    measurementCount (GenericQ5Geometry.wrapG L A)+751=measurementCount (GenericQ5Geometry.wrapG L B) := by
  simp only [GenericQ5Geometry.wrapG,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem gen_counts_delta (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+753=toffoliCount (Rolling1588BFFinal.gen L cx cy) ∧
    measurementCount (gen L cx cy)+751=measurementCount (Rolling1588BFFinal.gen L cx cy) := by
  rw [gen_shape,baseline_gen_shape]
  exact wrap_counts_delta L _ _ (generic_counts_delta L hw cx cy)

theorem gen_slots_delta (L : ControlledPointLayout) (cx cy : Fp) :
    gateSlots (gen L cx cy)≤ gateSlots (Rolling1588BFFinal.gen L cx cy)+50000 := by
  have d:=generic_slots_delta L cx cy
  rw [gen_shape,baseline_gen_shape]
  simp only [GenericQ5Geometry.wrapG,gateSlots_append,rename_gateSlots]
  omega

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset := by
  rw [gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (generic_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z:=zrep_physical L hn
  have c:=clrF_physical L hw hn
  have g:=gatePhysical_rename (swapF L) (swapF_injective L hw hn) _ (generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append] using And.intro (And.intro z (And.intro (And.intro c g) c)) z

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1588 := by
  rw [gen_shape]
  apply Rolling1588BFInventory.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy) _
    (generic_free layout layout_widths layout_nodup cx cy 768 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 718 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 719 (by simp)) C cy
  intro i hi
  apply generic_free layout layout_widths layout_nodup cx cy i
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

private theorem wrapper_counts_delta (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (A B : Program) (h : toffoliCount A+753=toffoliCount B ∧ measurementCount A+751=measurementCount B) :
    toffoliCount (Edges.wrapper L C cy A)+753=toffoliCount (Edges.wrapper L C cy B) ∧
    measurementCount (Edges.wrapper L C cy A)+751=measurementCount (Edges.wrapper L C cy B) := by
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2152593 := by
  have diff:=(wrapper_counts_delta layout (.some hc) cy _ _
    (gen_counts_delta layout layout_widths cx cy)).1
  have old:=Rolling1588BFFinal.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1499210 := by
  have diff:=(wrapper_counts_delta layout (.some hc) cy _ _
    (gen_counts_delta layout layout_widths cx cy)).2
  have old:=Rolling1588BFFinal.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50166097 := by
  have diff:=gen_slots_delta layout cx cy
  have old:=Rolling1588BFFinal.wrapper_slots C cx cy
  have lift : gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤
      gateSlots (Edges.wrapper layout C cy (Rolling1588BFFinal.gen layout cx cy))+50000 := by
    simp only [Edges.wrapper,Edges.finiteProgram,gateSlots_append,rename_gateSlots]
    omega
  omega

end ECDSAAdd.Entrant.ReflectionE1
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Final =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Resources

/-! Current Q1588 BF point with both E1 entries and one deleted reflection. -/
namespace ECDSAAdd.Entrant.ReflectionE1
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2152593,1499210,1588,50166097⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2152593 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C)≤1499210 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C)≤1588 := by
  cases C with
  | zero => change qubits []≤1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50166097 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1499210
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50166097
    rw [normalize_slots];exact program_gateSlots C


end ECDSAAdd.Entrant.ReflectionE1
end -- original module boundary

-- Selected checked E1+TickGap branch follows; merged entries, reflected square and inverse phases are preserved.

-- ===== ECDSAAdd.Submission.Entrant.TickGap1591Arithmetic =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.OneFlag

/-! TickGap arithmetic from public frontier8764679c, MainPre.lean.
The copied proof bodies and circuit definitions are unchanged.
The new-codec forward and phase transports are separate modules. -/

section
-- ===== TickGapBudget =====
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TickGap

theorem scaled_budget (p x i : Nat) (hx : x  ≤  p) :
    ∃ j k : Nat, j+k=i  ∧ 
      (SkywalkNat.step^[i] (SkywalkNat.init x p)).u * 2^j  ≤  p  ∧ 
      (SkywalkNat.step^[i] (SkywalkNat.init x p)).v * 2^k  ≤  p := by
  induction i with
  | zero => exact ⟨0,0,rfl,by simpa [SkywalkNat.init] using hx,by simp [SkywalkNat.init]⟩
  | succ i ih =>
    obtain ⟨j,k,hjk,hu,hv⟩ := ih
    rw [Function.iterate_succ_apply']
    generalize SkywalkNat.step^[i] (SkywalkNat.init x p)=z at hu hv ⊢
    by_cases hz : z.u=0
    · refine ⟨j+1,k,by omega,?_,?_⟩
      · simp [SkywalkNat.step,hz]
      · simpa [SkywalkNat.step,hz] using hv
    · by_cases he : z.u%2=0
      · refine ⟨j+1,k,by omega,?_,?_⟩
        · simp only [SkywalkNat.step,if_neg hz,if_pos he,pow_succ]
          have hhalf : z.u/2*2 ≤ z.u := by omega
          nlinarith [Nat.mul_le_mul_right (2^j) hhalf]
        · simpa [SkywalkNat.step,hz,he] using hv
      · by_cases hle : z.v ≤ z.u
        · refine ⟨j+1,k,by omega,?_,?_⟩
          · simp only [SkywalkNat.step,if_neg hz,if_neg he,if_pos hle,pow_succ]
            have hhalf : (z.u-z.v)/2*2 ≤ z.u := by omega
            nlinarith [Nat.mul_le_mul_right (2^j) hhalf]
          · simpa [SkywalkNat.step,hz,he,hle] using hv
        · refine ⟨k+1,j,by omega,?_,?_⟩
          · simp only [SkywalkNat.step,if_neg hz,if_neg he,if_neg hle,pow_succ]
            have hhalf : (z.v-z.u)/2*2 ≤ z.v := by omega
            nlinarith [Nat.mul_le_mul_right (2^k) hhalf]
          · simpa [SkywalkNat.step,hz,he,hle] using hu

private theorem two_pow_sum (a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    2^a+2^b ≤ 2^(a+b-1) := by
  obtain ⟨c,rfl⟩ : ∃ c, a=c+2 := ⟨a-2,by omega⟩
  obtain ⟨d,rfl⟩ : ∃ d, b=d+2 := ⟨b-2,by omega⟩
  have he : c+2+(d+2)-1=c+d+3 := by omega
  rw [he, pow_add, pow_add, pow_add]
  norm_num
  rw [pow_add]
  have hc : 1 ≤ 2^c := Nat.one_le_two_pow
  have hd : 1 ≤ 2^d := Nat.one_le_two_pow
  nlinarith [Nat.mul_le_mul hc hd]

private theorem scaled_lt (u p j : Nat) (hp : p < 2^256) (hu : u*2^j ≤ p) (hj : j ≤ 256) :
    u < 2^(256-j) := by
  have he : 2^(256-j)*2^j=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
  by_contra h
  have hle := Nat.mul_le_mul_right (2^j) (Nat.le_of_not_gt h)
  omega

/-- A strict fixed-modulus sum cap across the late 32-stage band. -/
theorem strict_sum_band (x p i : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p)
    (cop : x.Coprime p) (hi : 256 ≤ i  ∧  i ≤ 287) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
    z.u+z.v < 2^(511-i) := by
  dsimp only
  obtain ⟨j,k,hjk,hu,hv⟩ := scaled_budget p x i (Nat.le_of_lt hx)
  have valid := SkywalkNat.iter_valid i (SkywalkNat.init x p) hp0 hpo
  let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
  change z.u*2^j ≤ p at hu
  change z.v*2^k ≤ p at hv
  change 0 < z.v  ∧  z.v%2=1  ∧  z.u.gcd z.v=x.gcd p at valid
  change z.u+z.v < _
  by_cases hz : z.u=0
  · have hv1 : z.v=1 := by
      have hg := valid.2.2.trans cop
      rw [hz,Nat.gcd_zero_left] at hg
      exact hg
    have hi' : 1 ≤ 511-i := by omega
    have pow := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) hi'
    simp only [pow_one] at pow
    omega
  have hu0 : 1 ≤ z.u := by omega
  have hv0 : 1 ≤ z.v := by omega
  have hj : j ≤ 255 := by
    by_contra h
    have hpw := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) (show 256 ≤ j by omega)
    nlinarith
  have hk : k ≤ 255 := by
    by_contra h
    have hpw := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) (show 256 ≤ k by omega)
    nlinarith
  have ju := scaled_lt z.u p j hp hu (by omega)
  have kv := scaled_lt z.v p k hp hv (by omega)
  by_cases hje : j=255
  · have ue : z.u=1 := by simp only [hje] at ju; norm_num at ju; omega
    have kk : k=i-255 := by omega
    have kp : k ≤ 32 := by omega
    have kp32 := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) kp
    have ep : 2^(256-k)*2^k=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
    have ek : 511-i=256-k := by omega
    rw [ue,ek]
    by_contra h
    have hbig : 2^(256-k) ≤ z.v+1 := by omega
    have mul := Nat.mul_le_mul_right (2^k) hbig
    nlinarith
  · by_cases hke : k=255
    · have ve : z.v=1 := by simp only [hke] at kv; norm_num at kv; omega
      have jj : j=i-255 := by omega
      have jp : j ≤ 32 := by omega
      have jp32 := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) jp
      have ep : 2^(256-j)*2^j=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
      have ek : 511-i=256-j := by omega
      rw [ve,ek]
      by_contra h
      have hbig : 2^(256-j) ≤ z.u+1 := by omega
      have mul := Nat.mul_le_mul_right (2^j) hbig
      nlinarith
    · have a : 2 ≤ 256-j := by omega
      have b : 2 ≤ 256-k := by omega
      have bound := two_pow_sum (256-j) (256-k) a b
      have e : (256-j)+(256-k)-1=511-i := by omega
      rw [e] at bound
      omega
end ECDSAAdd.Entrant.TickGap

end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def signedAddTop (q : Wire) (x y carry : List Wire) : Program :=
  signComplement q x ++ TopCarry.addInPlaceTop x y carry q ++ signComplement q x

def Shape (n V : Nat) : Prop := V < 2^n ∨ 3*2^n ≤ V

theorem shape_complement (n V : Nat) (hv : V < 2^(n+2)) (h : Shape n V) :
    Shape n (2^(n+2)-1-V) := by
  have pow : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  unfold Shape at *
  omega

theorem shape_of_signed (n V : Nat) (hv : V < 2^(n+2))
    (lo : -((2^n:Nat):Int) ≤ signedDecode (n+2) V)
    (hi : signedDecode (n+2) V < ((2^n:Nat):Int)) : Shape n V := by
  have p2 : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  have p1 : 2^(n+2-1) = 2*2^n := by rw [show n+2-1=n+1 by omega,pow_succ]; ring
  unfold signedDecode at lo hi
  split_ifs at lo hi <;> unfold Shape <;> omega

theorem signedAddTop_eq (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (clean : ∀ w ∈ cs, s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Shape n (regValue y (run (signedAdd q x y cs) [] s).basis)) :
    run (signedAddTop q x y cs) m s=run (signedAdd q x y cs) m s := by
  have hxnd : x.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1).1
  have qx : q∉x := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have dis : List.Disjoint x (y++cs) := by
    have h : (x++(y++cs)).Nodup := by simpa only [List.append_assoc] using (List.nodup_cons.mp hn).2
    exact (List.nodup_append'.mp h).2.2
  have zx := (signComplement_counts q x).2
  let u := run (signComplement q x) [] s
  have fan := signComplement_correct q x hxnd qx s []
  have ux : Shape n (regValue x u.basis) := by
    change Shape n (regValue x (run (signComplement q x) [] s).basis)
    rw [fan.2.2]
    cases hs : s.basis q
    · exact source
    · simpa only [hx,if_true] using shape_complement n _ (by simpa [hx] using regValue_lt x s.basis) source
  have clean' : ∀ w ∈ cs, u.basis w=false := by
    intro w hw
    exact (fan.2.1 w (fun h => List.disjoint_left.mp dis h (List.mem_append_right _ hw))).trans (clean w hw)
  have out (r : List Bool) :
      regValue y (run (signComplement q x) r (run (addInPlace x y cs q) r u)).basis =
      regValue y (run (addInPlace x y cs q) r u).basis := by
    have h := signComplement_correct q x hxnd qx (run (addInPlace x y cs q) r u) r
    apply regValue_congr
    intro w hw
    exact h.2.1 w (fun hxw => List.disjoint_left.mp dis hxw (List.mem_append_left _ hw))
  have old : regValue y (run (signedAdd q x y cs) [] s).basis =
      regValue y (run (addInPlace x y cs q) [] u).basis := by
    simp only [signedAdd,List.append_assoc]
    rw [TopCarry.run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  have add := addInPlace_correct x y cs q hn (hx.trans hy.symm) hc u [] clean'
  have us : Shape n ((regValue x u.basis+regValue y u.basis+(u.basis q).toNat)%2^(n+2)) := by
    rw [old,add.2.2,hy] at sum
    exact sum
  have eq (r : List Bool) := TopCarry.addInPlaceTop_eq n x y cs q hy (hx.trans hy.symm)
    hc hn u r clean' ux us
  simp only [signedAddTop,signedAdd,List.append_assoc]
  rw [TopCarry.run_zero_head _ _ m s zx,TopCarry.run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq]
  have mc := TopCarry.addInPlaceTop_counts n x y cs q hy (hx.trans hy.symm) hc
  have mo := addInPlace_counts x y cs q (hx.trans hy.symm) hc
  rw [mc.2,mo.2,hy]
  rfl
end ECDSAAdd.Entrant.TickGap
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def recordTop (sx sy q : Wire) (x y cs : List Wire) : Program :=
  skywalkSignToggle sx sy q ++ signedAddTop q x y cs ++ skywalkSignToggle sx sy q

theorem signedAddTop_counts (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length) :
    toffoliCount (signedAddTop q x y cs)=n ∧ measurementCount (signedAddTop q x y cs)=n+1 := by
  have h := TopCarry.addInPlaceTop_counts n x y cs q hy (hx.trans hy.symm) hc
  simp only [signedAddTop,toffoliCount_append,measurementCount_append,
    (signComplement_counts q x).1,(signComplement_counts q x).2,h.1,h.2]
  exact ⟨by omega,by omega⟩

theorem toggle_frame (sx sy q : Wire) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (w : Wire) (hw : w≠q) :
    (run (skywalkSignToggle sx sy q) m s).basis w=s.basis w := by
  rw [skywalkSignToggle_correct sx sy q hqx hqy]
  simp [writeBit,hw]

theorem recordTop_eq (n : Nat) (sx sy q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (clean : ∀w∈cs,s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Shape n (regValue y (run (signedRecord sx sy q x y cs) [] s).basis)) :
    run (recordTop sx sy q x y cs) m s=run (signedRecord sx sy q x y cs) m s := by
  have qrest := (List.nodup_cons.mp hn).1
  have away (w : Wire) (hw : w∈x++y++cs) : w≠q := by
    intro he; subst w; exact qrest hw
  let u := run (skywalkSignToggle sx sy q) [] s
  have ut (w : Wire) (hw : w≠q) : u.basis w=s.basis w := toggle_frame sx sy q hqx hqy s [] w hw
  have ux : regValue x u.basis=regValue x s.basis :=
    regValue_congr _ _ _ (fun w hw => ut w (away w (by simp [hw])))
  have uc : ∀w∈cs,u.basis w=false := by
    intro w hw
    exact (ut w (away w (by simp [hw]))).trans (clean w hw)
  have zx := (skywalkSignToggle_counts sx sy q).2
  have out (r : List Bool) :
      regValue y (run (skywalkSignToggle sx sy q) r (run (signedAdd q x y cs) r u)).basis =
      regValue y (run (signedAdd q x y cs) r u).basis :=
    regValue_congr _ _ _ (fun w hw => toggle_frame sx sy q hqx hqy _ r w (away w (by simp [hw])))
  have old : regValue y (run (signedRecord sx sy q x y cs) [] s).basis =
      regValue y (run (signedAdd q x y cs) [] u).basis := by
    simp only [signedRecord,List.append_assoc]
    rw [TopCarry.run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  rw [old] at sum
  have eq (r : List Bool) := signedAddTop_eq n q x y cs hx hy hc hn u r uc (ux ▸ source) sum
  have mc := (signedAddTop_counts n q x y cs hx hy hc).2
  have mo := (signedWord_counts q x y cs (hx.trans hy.symm) hc).2.1
  simp only [recordTop,signedRecord,List.append_assoc]
  rw [TopCarry.run_zero_head _ _ m s zx,TopCarry.run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq,mc,mo,hy]
  rfl
end ECDSAAdd.Entrant.TickGap
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def narrowTop (L : NarrowSignedRecordLayout) (n : Nat) : Program :=
  recordTop L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1)) ++
    signComplement L.q (L.y.drop n)

theorem record_source (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0) :
    regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) m s).basis = regValue L.xp s.basis := by
  have h := signedRecord_spec L.xlo L.ylo L.sx L.sy L.q L.carryLow (L.short_nodup hn)
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
    (signedRegValue L.xp s.basis) (signedRegValue L.yp s.basis) s m ⟨hq,rfl,rfl,clean⟩
  have eq := (signedRegValue_eq_iff L.xp _ _).mp h.2.2.1
  exact regValue_congr _ _ _ eq

theorem narrowTop_eq (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) (s : State) (m : List Bool)
    (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0)
    (source : Shape n (regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis))
    (sum : Shape n (regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis)) :
    run (narrowTop L (n+2)) m s=run (narrowSignedRecord L (n+2)) m s := by
  have views := L.views (n+2) hw
  have clean' : ∀w∈L.carryLow,s.basis w=false := (regValue_zero _ _).mp clean
  have qx : L.sx≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have fan (r : List Wire) (hr : ∀w∈r,w∉L.yhigh) (v : State) (record : List Bool) :
      regValue r (run (signComplement L.q L.yhigh) record v).basis=regValue r v.basis := by
    have f := signComplement_correct L.q L.yhigh (L.high_nodup hn) (L.q_high hn) v record
    exact regValue_congr _ _ _ (fun w hw => f.2.1 w (hr w hw))
  have xaway : ∀w∈L.xp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp only [NarrowSignedRecordLayout.x,List.mem_append] at *; tauto)
  have yaway : ∀w∈L.yp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp [hw'])
  have outx : regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.xp xaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  have outy : regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.yp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.yp yaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  rw [outx,record_source L (n+2) hw hn s [] hq clean] at source
  rw [outy] at sum
  have eq (r : List Bool) := recordTop_eq n L.sx L.sy L.q L.xp L.yp L.carryLow
    hw.x hw.y (hw.carry.trans hw.y.symm) (L.short_nodup hn) qx qy s r clean' source sum
  have mc := signedAddTop_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have rz := (skywalkSignToggle_counts L.sx L.sy L.q).2
  have old := (signedWord_counts L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)).2.1
  have counts : measurementCount (recordTop L.sx L.sy L.q L.xp L.yp L.carryLow)=
      measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) := by
    simp only [recordTop,signedRecord,measurementCount_append,rz,mc.2,old,hw.y]
    omega
  simp only [narrowTop,narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
  rw [run_append,run_append,run_take,run_take,eq,counts]
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic Baselines Challenge RecordedQuantum

theorem signedAddTop_support (q : Wire) (x y cs : List Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    wires (signedAddTop q x y cs) ⊆ wires (signedAdd q x y cs) := by
  rw [(signedWord_wires q x y cs hx hc).1]
  have fan : wires (signComplement q x) ⊆ (q::(x++y++cs)).toFinset := by
    intro w hw
    have h := signComplement_wires_subset q x hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  simp only [signedAddTop,wires_append,Finset.union_subset_iff]
  exact ⟨⟨fan,TopCarry.addInPlaceTop_wires x y cs q⟩,fan⟩

theorem narrowTop_counts (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    toffoliCount (narrowTop L (n+2))+1=toffoliCount (narrowSignedRecord L (n+2)) ∧
      measurementCount (narrowTop L (n+2))=measurementCount (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have h := signedAddTop_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have old := narrowSignedRecord_counts L (n+2) hw
  have z := skywalkSignToggle_counts L.sx L.sy L.q
  have f := signComplement_counts L.q L.yhigh
  simp only [narrowTop,recordTop,v.1,v.2.1,v.2.2.1,v.2.2.2,
    toffoliCount_append,measurementCount_append,z.1,z.2,h.1,h.2,f.1,f.2,old.1,old.2.1]
  exact ⟨by omega,by omega⟩

theorem narrowTop_support (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    wires (narrowTop L (n+2)) ⊆ wires (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have sub := signedAddTop_support L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  simp only [narrowTop,narrowSignedRecord,recordTop,signedRecord,v.1,v.2.1,v.2.2.1,v.2.2.2,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) sub)
    (Finset.Subset.refl _)) (Finset.Subset.refl _)

theorem signedAddTop_physical (q : Wire) (x y cs : List Wire) (hn : (q::(x++y++cs)).Nodup) :
    GatePhysical (signedAddTop q x y cs) := by
  have qx : q∉x := fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
  have fan := signComplement_physical q x qx
  have top := TopCarry.addInPlaceTop_physical x y cs q hn
  simp only [signedAddTop,gatePhysical_append]
  exact ⟨⟨fan,top⟩,fan⟩

theorem narrowTop_physical (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) : GatePhysical (narrowTop L (n+2)) := by
  have v := L.views (n+2) hw
  have nd := L.short_nodup hn
  have qx : L.sx≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have toggle : GatePhysical (skywalkSignToggle L.sx L.sy L.q) := by
    simp [skywalkSignToggle,GatePhysical,PhysicalInstr,ProperGate,qx,qy]
  have top := signedAddTop_physical L.q L.xp L.yp L.carryLow nd
  have fan := signComplement_physical L.q L.yhigh (L.q_high hn)
  simp only [narrowTop,recordTop,v.1,v.2.1,v.2.2.1,v.2.2.2,gatePhysical_append]
  exact ⟨⟨⟨toggle,top⟩,toggle⟩,fan⟩

theorem top_slots_le_old (x y cs : List Wire) (c : Wire) :
    gateSlots (TopCarry.addInPlaceTop x y cs c) ≤ gateSlots (addInPlace x y cs c) := by
  induction x generalizing y cs c with
  | nil => simp [TopCarry.addInPlaceTop,addInPlace]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [TopCarry.addInPlaceTop,addInPlace]
      | cons b bs => cases bs <;> simp [TopCarry.addInPlaceTop,addInPlace]
    | cons a' as =>
      cases y with
      | nil => simp [TopCarry.addInPlaceTop,addInPlace]
      | cons b bs =>
        cases bs with
        | nil => simp [TopCarry.addInPlaceTop,addInPlace]
        | cons b' bs =>
          cases cs with
          | nil => simp [TopCarry.addInPlaceTop,addInPlace]
          | cons d ds =>
            have h := ih (b'::bs) ds d
            simp only [TopCarry.addInPlaceTop,addInPlace,gateSlots_append] at h ⊢
            split_ifs <;> simp only [majority_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots] at h ⊢ <;> omega

theorem narrowTop_slots (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    gateSlots (narrowTop L (n+2)) ≤ gateSlots (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have top := top_slots_le_old L.xp L.yp L.carryLow L.q
  simp only [narrowTop,narrowSignedRecord,recordTop,signedRecord,signedAddTop,signedAdd,
    v.1,v.2.1,v.2.2.1,v.2.2.2,gateSlots_append]
  omega
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

/-- The two post-tick signed values fit below the strict late-stage cap. -/
theorem band_step_values (x p i : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p) (cop : x.Coprime p)
    (hi : 255 ≤ i  ∧  i ≤ 286) :
    let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int));
    let n := W.compactSkywalkTickPostWidth i-2;
    -((2^n:Nat):Int)  ≤  (SkywalkRails.step r).h  ∧  (SkywalkRails.step r).h  <  ((2^n:Nat):Int)  ∧ 
    -((2^n:Nat):Int)  ≤  (SkywalkRails.step r).k  ∧  (SkywalkRails.step r).k  <  ((2^n:Nat):Int) := by
  dsimp only
  have nw : W.compactSkywalkTickPostWidth i-2=510-i := by
    unfold W.compactSkywalkTickPostWidth W.narrowSkywalkWidth
    omega
  rw [nw]
  have cap := strict_sum_band x p (i+1) hp0 hpo hp gap hx cop (by omega)
  obtain ⟨G,S,enc⟩ := SkywalkTrace.iter_encoded (i+1) false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at enc
  rw [Function.iterate_succ_apply'] at enc
  let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
  let z := SkywalkNat.step^[i+1] (SkywalkNat.init x p)
  change SkywalkTrace.next r=SkywalkRails.encode G S (z.u:Int) (z.v:Int) at enc
  change z.u+z.v < 2^(511-(i+1)) at cap
  have exp : 511-(i+1)=510-i := by omega
  rw [exp] at cap
  have abs := SkywalkRails.encode_abs_sum_bound G S z.u z.v (z.u+z.v) (Nat.le_refl _)
  rw [←enc] at abs
  change |(SkywalkRails.step r).h|  ≤  ((z.u+z.v:Nat):Int)  ∧ 
    |(SkywalkRails.step r).k|  ≤  ((z.u+z.v:Nat):Int) at abs
  have cap' : ((z.u+z.v:Nat):Int) < ((2^(510-i):Nat):Int) := by exact_mod_cast cap
  have ah := abs_le.mp abs.1
  have ak := abs_le.mp abs.2
  dsimp only [r] at ah ak
  exact ⟨by omega,by omega,by omega,by omega⟩

theorem repaired_output_shape (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p) (cop : x.Coprime p)
    (hi : 255 ≤ i  ∧  i ≤ 286) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    let L := W.compactSkywalkTickLayout w i;
    let n := W.compactSkywalkTickPostWidth i;
    Shape (n-2) (regValue (L.half.take n) (run (W.repairedTick w i) m s).basis)  ∧ 
      Shape (n-2) (regValue (L.b.take n) (run (W.repairedTick w i) m s).basis) := by
  dsimp only
  have hgap : p+2^32 ≤ 2^256 := Nat.le_of_lt gap
  rw [W.repairedTick_eq w hn x p i hp0 hx0 hpo hp hgap hx cop (by omega) s m hs]
  have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hgap hx cop (by omega) s hs
  have fit := W.narrowSkywalk_iter_fit x p i hp0 hx0 hpo hp hgap hx cop (by omega)
  have out := W.compactSkywalkTickOutput_spec w i (by omega) hn _ _ _ fit.1 fit.2.1 fit.2.2.1 fit.2.2.2.1 fit.2.2.2.2 s [] input
  have bounds := band_step_values x p i hp0 hpo hp gap hx cop hi
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  have ns : n-2+2=n := by
    have width := W.compactSkywalkTick_width_bounds i (by omega)
    dsimp only [n]
    omega
  have lenA : n ≤ L.half.length := by
    rw [W.compactSkywalkTick_half w i (by omega),wireBlock_length]
    exact (W.compactSkywalkTick_width_bounds i (by omega)).2.2.1
  have lenB : n ≤ L.b.length := by
    rw [W.compactSkywalkTick_b w i (by omega),wireBlock_length]
    exact (W.compactSkywalkTick_width_bounds i (by omega)).2.2.1
  have aview : (W.compactSkywalkTickARelease w i).retained=L.half.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) lenA
  have bview : (W.compactSkywalkTickBRelease w i).retained=L.b.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) lenB
  have a := out.2.1
  have b := out.2.2.1
  rw [aview] at a
  rw [bview] at b
  have lenA' : (L.half.take n).length=n := by simp [List.length_take,Nat.min_eq_left lenA]
  have lenB' : (L.b.take n).length=n := by simp [List.length_take,Nat.min_eq_left lenB]
  unfold signedRegValue at a b
  rw [lenA'] at a
  rw [lenB'] at b
  change Shape (n-2) (regValue (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis) ∧
    Shape (n-2) (regValue (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis)
  constructor
  · apply shape_of_signed (n-2) _ (by simpa [ns,lenA'] using regValue_lt (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis)
    · rw [ns,a]; exact bounds.1
    · rw [ns,a]; exact bounds.2.1
  · apply shape_of_signed (n-2) _ (by simpa [ns,lenB'] using regValue_lt (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis)
    · rw [ns,b]; exact bounds.2.2.1
    · rw [ns,b]; exact bounds.2.2.2
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def head (w : Nat → Wire) (i : Nat) : Program :=
  let L := W.compactSkywalkTickLayout w i
  (if i=224 ∨ (256 ≤ i  ∧  i ≤ 509) then W.repairedRoute L
    else skywalkRoute L.a0 L.b0 L.ah L.bh) ++ skywalkSignedHalf L.aSign L.ext

def tail (w : Nat → Wire) (i : Nat) : Program :=
  [.CX (W.compactSkywalkTickLayout w i).previous (W.compactSkywalkTickLayout w i).a0] ++
    W.compactSkywalkTickCleanup w i

def tick (w : Nat → Wire) (i : Nat) : Program :=
  if 255 ≤ i  ∧  i ≤ 286 then
    head w i ++ narrowTop (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
      (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i
  else W.repairedTick w i

theorem old_split (w : Nat → Wire) (i : Nat) (band : 255 ≤ i  ∧  i ≤ 286) :
    W.repairedTick w i = head w i ++
      narrowSignedRecord (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
        (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i := by
  have nf : ¬ W.fwdTrim i := by unfold W.fwdTrim; omega
  simp only [W.repairedTick,if_neg nf,W.repairedTick0,head,tail,W.compactSkywalkTick,narrowSkywalkTick]
  split_ifs  <;> simp only [List.append_assoc]

theorem repairedRoute_small_support (L : SkywalkIntegerLayout) (hv : L.Valid) (hpos : 0 < L.bMid.length) :
    wires (W.repairedRoute L) ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
  have lo := swapRegisters_wires L.a0 L.aMid L.bMid hv.mids
  have tm : L.bMid.getD (L.bMid.length-1) 0∈L.bMid := W.repair_member_getD _ _ (by omega)
  have ls : wires (swapRegisters L.a0 L.aMid L.bMid) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    have h := lo hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh] at h ⊢
    tauto
  have ss : wires (W.signRepair L.aSign L.bSign L.previous (L.bMid.getD (L.bMid.length-1) 0)) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [W.signRepair,wires,Instr.wires,correctionWires,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh,
      List.not_mem_nil,or_false]
    have ht : q=L.bMid.getD (L.bMid.length-1) 0 → q∈L.bMid := fun he => he ▸ tm
    tauto
  have cx : wires [.CX L.a0 L.b0] ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  simp only [W.repairedRoute,W.repairedSwap,wires_append,Finset.union_subset_iff]
  exact ⟨⟨ls,ss⟩,cx⟩

theorem head_aux (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).history::(W.compactSkywalkTickLayout w i).carry) :
    (run (head w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have hpos : 0 < L.bMid.length := by
    change 0 < (wireBlock w 771 (W.compactSkywalkTickPreWidth i-2)).length
    rw [wireBlock_length]
    have width := W.compactSkywalkTick_width_bounds i hi
    omega
  have dis : List.Disjoint (L.history::L.carry) (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)) := by
    have nd : ((L.history::L.carry)++(L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh))).Nodup := by
      apply List.nodup_iff_count.mpr
      intro a
      have h := List.nodup_iff_count.mp hv.nodup a
      simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at h ⊢
      omega
    exact (List.nodup_append'.mp nd).2.2
  have qaway : q∉L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh) := List.disjoint_left.mp dis hq
  have sup : wires (head w i) ⊆ (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    have inc : (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [List.mem_toFinset,List.mem_cons] at ha ⊢
      tauto
    have repair := (repairedRoute_small_support L hv hpos).trans inc
    have full : wires (skywalkRoute L.a0 L.b0 L.ah L.bh) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      have h := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
      tauto
    have half : wires (skywalkSignedHalf L.aSign L.ext) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [skywalkSignedHalf,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.notMem_empty,or_false] at ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,List.mem_singleton]
      tauto
    simp only [head,wires_append,Finset.union_subset_iff]
    split_ifs  <;> exact ⟨by assumption,half⟩
  exact run_preserves_outside _ _ _ _ (fun h => qaway (List.mem_toFinset.mp (sup h)))

theorem tail_prefix (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).half.take (W.compactSkywalkTickPostWidth i) ++
      (W.compactSkywalkTickLayout w i).b.take (W.compactSkywalkTickPostWidth i)) :
    (run (tail w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have words := W.compactSkywalkTick_words_disjoint w i hi hn
  have nd := (List.nodup_cons.mp (L.record_nodup hv)).2
  have wa : L.half.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).1
  have wb : L.b.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.1
  have adot : List.Disjoint (L.half.take n) (L.half.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wa
  have bdot : List.Disjoint (L.b.take n) (L.b.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wb
  have apart : q∉L.half.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact List.disjoint_left.mp adot hqa
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_drop h) (List.mem_of_mem_take hqb)
  have bpart : q∉L.b.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_take hqa) (List.mem_of_mem_drop h)
    · exact List.disjoint_left.mp bdot hqb
  have q0 : q≠L.a0 := by
    have qm : q∈L.half++L.b := by
      rcases List.mem_append.mp hq with hqa|hqb
      · exact List.mem_append_left _ (List.mem_of_mem_take hqa)
      · exact List.mem_append_right _ (List.mem_of_mem_take hqb)
    intro he
    subst q
    have h := List.nodup_iff_count.mp hv.nodup L.a0
    have hq' := List.count_pos_iff.mpr qm
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,List.count_nil,List.count_cons,List.count_append,
      List.count_singleton] at h hq'
    simp only [beq_self_eq_true,if_true] at h
    omega
  have valid := W.compactSkywalkTick_release_valid w i hi hn
  have af (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickARelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.1 v r).2.1 q apart
  have bf (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickBRelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.2 v r).2.1 q bpart
  simp only [tail,W.compactSkywalkTickCleanup,run_append,run_take]
  rw [bf,af]
  change Function.update s.basis L.a0 (s.basis L.a0 ^^ s.basis L.previous) q = s.basis q
  exact Function.update_of_ne q0 _ _
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

theorem tick_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p) (cop : x.Coprime p) (hi : i < 512)
    (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (tick w i) m s=run (W.repairedTick w i) m s := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    let P := head w i
    let Q := narrowSignedRecord R n
    let E := tail w i
    let u := run P (m.take (measurementCount P)) s
    let v := run Q (m.drop (measurementCount P)) u
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have width := W.compactSkywalkTick_width_bounds i hi
    have npos : 2 ≤ n := width.2.1
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have nd : R.wires.Nodup := narrowSkywalkRecord_nodup L hv n (by omega) nlen
    have n2 : n-2+2=n := by omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have whole : run (W.repairedTick w i) m s=
        run E ((m.drop (measurementCount P)).drop (measurementCount Q)) v := by
      rw [old_split _ _ band,List.append_assoc,run_append,run_take,run_append,run_take]
      simp only [P,Q,E,u,v,run_take]
      rfl
    have sizes := repaired_output_shape w hn x p i hp0 hx0 hpo hp gap hx cop band s m hs
    have keep (r : List Wire) (hr : r⊆L.half.take n++L.b.take n) :
        regValue r (run (W.repairedTick w i) m s).basis=regValue r v.basis := by
      rw [whole]
      apply regValue_congr
      intro q hq
      exact tail_prefix w i hi hn v _ q (hr hq)
    have shapeX : Shape (n-2) (regValue (L.half.take n) v.basis) := by
      rw [←keep _ (by intro q hq; exact List.mem_append_left _ hq)]
      exact sizes.1
    have shapeY : Shape (n-2) (regValue (L.b.take n) v.basis) := by
      rw [←keep _ (by intro q hq; exact List.mem_append_right _ hq)]
      exact sizes.2
    have record0 : (run Q [] u).basis=v.basis := run_basis_records Q u u [] (m.drop (measurementCount P)) rfl
    have orig := narrowSkywalkRecord_views L hv n (by omega) nlen
    have views := R.views n hw
    have xx : R.xp=L.half.take n := by rw [←views.1]; rw [orig.1]
    have yy : R.yp=L.b.take n := by rw [←views.2.1]; rw [orig.2.1]
    have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp (Nat.le_of_lt gap) hx cop hi s hs
    have uq : u.basis R.q=false := by
      apply (head_aux w i hi hn s _ L.history (List.mem_cons_self)).trans
      exact input.2.2.2.2.1
    have clean : regValue R.carryLow u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have qm : q∈L.carry := List.mem_of_mem_take hq
      apply (head_aux w i hi hn s _ q (List.mem_cons_of_mem _ qm)).trans
      exact (regValue_zero _ _).mp input.2.2.2.2.2 q qm
    have eq (r : List Bool) : run (narrowTop R n) r u=run Q r u := by
      have a : Shape (n-2) (regValue R.xp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,xx,record0]
        exact shapeX
      have b : Shape (n-2) (regValue R.yp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,yy,record0]
        exact shapeY
      simpa only [n2] using narrowTop_eq (n-2) R hw' nd u r uq clean a b
    have counts : measurementCount (narrowTop R n)=measurementCount Q := by
      simpa only [n2] using (narrowTop_counts (n-2) R hw').2
    simp only [tick,if_pos band]
    rw [old_split _ _ band]
    change run ((P++narrowTop R n)++E) m s=run ((P++Q)++E) m s
    conv_lhs => rw [List.append_assoc,run_append P (narrowTop R n++E)]
    conv_rhs => rw [List.append_assoc,run_append P (Q++E)]
    change run (narrowTop R n++E) (m.drop (measurementCount P)) u = run (Q++E) (m.drop (measurementCount P)) u
    rw [run_append (narrowTop R n) E,run_append Q E]
    rw [run_take (narrowTop R n),run_take Q,eq,counts]
  · simp only [tick,if_neg band]

def due (i : Nat) : Nat := if 255 ≤ i  ∧  i ≤ 286 then 1 else 0

theorem tick_counts (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (tick w i)+due i=toffoliCount (W.repairedTick w i)  ∧ 
    measurementCount (tick w i)=measurementCount (W.repairedTick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_counts (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,due,if_pos band,toffoliCount_append,measurementCount_append]
    exact ⟨by omega,by omega⟩
  · simp only [tick,if_neg band,due,if_neg band,Nat.add_zero,and_self]

theorem tick_support (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    wires (tick w i) ⊆ wires (W.repairedTick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_support (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)
  · simp only [tick,if_neg band]
    exact Finset.Subset.refl _

theorem tick_slots (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    Challenge.gateSlots (tick w i)  ≤  Challenge.gateSlots (W.repairedTick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_slots (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,Challenge.gateSlots_append]
    omega
  · simp only [tick,if_neg band]
    exact Nat.le_refl _

theorem tick_physical (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (tick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_physical (n-2) R hw' (narrowSkywalkRecord_nodup L hv n (by omega) nlen)
    simp only [n2] at h
    dsimp only [R,n,L] at h
    have old := W.repairedTick_physical w i hi hn
    rw [old_split _ _ band] at old
    simp only [tick,if_pos band,gatePhysical_append] at old ⊢
    exact ⟨⟨old.1.1,h⟩,old.2⟩
  · simpa only [tick,if_neg band] using W.repairedTick_physical w i hi hn
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic MappedCompressed Secp256k1 History5 OB5

theorem tick_eq5 (x : Nat) (hx0 : 0 < x) (hx : x < p) (i : Nat) (hi : i < 512)
    (s : State) (m : List Bool) (hs : W.CompressedCompactStage5 base x p i s.basis) :
    run (tick base i) m s=run (W.repairedTick base i) m s := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  have dis := Stack5.prefix_disjoint_layout base base_pool_nodup i i (Nat.le_refl i) hi
  have read : ∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset,s.basis q=raw.basis q := by
    intro q hq
    rw [hbits]
    exact run_preserves_outside _ _ _ q (fun he => Finset.disjoint_left.mp dis he hq)
  have old := W.repairedTick_support base i hi base_pool_nodup
  have fresh := (tick_support base i hi base_pool_nodup).trans old
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 < 2^256 := by norm_num [p]
  exact Stack5.local_replace _ _ _ fresh old s raw m m read
    (tick_eq base base_pool_nodup x p i hp0 hx0 hpo hp gap hx cop hi raw m hraw)

end ECDSAAdd.Entrant.TickGap
end
end -- original module boundary

-- ===== IntegerTickRanges (ArthurOstapenko baaabf50, ported) =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TickRanges

def H : Nat := 2^255

theorem classify (x p i : Nat) (hx0 : 0<x) (hx : x<p) (hpodd : p%2=1)
    (hp : p<2^256) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
    z.u+z.v < H   ∨
    (z.v=p   ∧   z.u*2^i=x)   ∨
    (∃ t r : Nat, t+r=i   ∧   1  ≤  r   ∧   z.v*2^t=x   ∧   z.u*2^r+z.v=p   ∧   z.u+z.v<p) := by
  induction i with
  | zero =>
    exact Or.inr (Or.inl ⟨rfl,by simp [SkywalkNat.init]⟩)
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    generalize heq : SkywalkNat.step^[i] (SkywalkNat.init x p)=z at ih ⊢
    rcases ih with hs | hno | hone
    · exact Or.inl ((SkywalkNat.step_sum_nonincrease z).trans_lt hs)
    · obtain ⟨hv,hu⟩ := hno
      have hz : z.u  ≠  0 := by intro h; simp [h] at hu; omega
      have hul : z.u<p := by
        have hi : 1  ≤  2^i := Nat.one_le_two_pow
        nlinarith
      by_cases he : z.u%2=0
      · right; left
        refine ⟨by simp [SkywalkNat.step,hz,he,hv],?_⟩
        simp only [SkywalkNat.step,if_neg hz,if_pos he,pow_succ]
        have hh : z.u/2*2=z.u := by omega
        calc
          _ = (z.u/2*2)*2^i := by ring
          _ = x := by rw [hh,hu]
      · right; right
        have hodd : z.u%2=1 := by omega
        have hdiff : (p-z.u)/2*2=p-z.u := by omega
        refine ⟨i,1,by omega,by omega,?_,?_,?_⟩
        all_goals simp only [SkywalkNat.step,if_neg hz,if_neg he,hv,
          if_neg (show   ¬  p  ≤  z.u by omega)]
        · exact hu
        · norm_num; omega
        · omega
    · obtain ⟨t,r,htr,hr,hv,hu,hs⟩ := hone
      have vz : z.v  ≤  x := by
        have ht : 1  ≤  2^t := Nat.one_le_two_pow
        nlinarith
      have hz : z.u  ≠  0 := by intro h; simp [h] at hu; omega
      have valid := SkywalkNat.iter_valid i (SkywalkNat.init x p) (show 0<p from by omega) hpodd
      rw [heq] at valid
      have vo : z.v%2=1 := valid.2.1
      by_cases he : z.u%2=0
      · right; right
        refine ⟨t,r+1,by omega,by omega,?_,?_,?_⟩
        all_goals simp only [SkywalkNat.step,if_neg hz,if_pos he]
        · exact hv
        · rw [pow_succ]
          have hh : z.u/2*2=z.u := by omega
          calc
            _ = (z.u/2*2)*2^r+z.v := by ring
            _ = p := by rw [hh,hu]
        · omega
      · left
        unfold SkywalkNat.step
        rw [if_neg hz,if_neg he]
        have hpH : p<2*H := by simpa [H,pow_succ] using hp
        split_ifs <;> dsimp only <;> omega

theorem early_gap (x i : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (hi : 225  ≤  i   ∧   i  ≤  254) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)
    z.u+z.v < H   ∨   H  ≤  z.v := by
  have hp : ECDSAAdd.p<2^256 := by norm_num [ECDSAAdd.p]
  have hpodd : ECDSAAdd.p%2=1 := by norm_num [ECDSAAdd.p]
  have hpe : ECDSAAdd.p+(2^32+977)=2*H := by norm_num [ECDSAAdd.p,H]
  obtain hs | hno | hone := classify x ECDSAAdd.p i hx0 hx hpodd hp
  · exact Or.inl hs
  · exact Or.inr (by rw [hno.1]; norm_num [ECDSAAdd.p,H])
  · obtain ⟨t,r,htr,hr,hv,hu,_⟩ := hone
    by_cases ht : 2  ≤  t
    · by_cases hr2 : 2  ≤  r
      · left
        have tp : 4  ≤  2^t := by simpa using Nat.pow_le_pow_right (by decide : 1  ≤  (2:Nat)) ht
        have rp : 4  ≤  2^r := by simpa using Nat.pow_le_pow_right (by decide : 1  ≤  (2:Nat)) hr2
        have hsmall : 4*((SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).u+
            (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).v)<2*ECDSAAdd.p := by nlinarith
        nlinarith
      · have re : r=1 := by omega
        have tt : 224  ≤  t := by omega
        have tp : 2^224  ≤  2^t := Nat.pow_le_pow_right (by decide) tt
        left
        rw [re] at hu
        norm_num at hu
        have vle : (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).v<2^32 := by
          by_contra hh
          have vv : 2^32  ≤  (SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)).v := by omega
          have mul := Nat.mul_le_mul vv tp
          norm_num at mul
          nlinarith
        nlinarith
    · have rr : 224  ≤  r := by omega
      have rle : r  ≤  254 := by omega
      have rp : 2^224  ≤  2^r := Nat.pow_le_pow_right (by decide) rr
      have rpbig : 2^32+977<2^r := by
        calc
          2^32+977 < 2^224 := by norm_num
          _   ≤   2^r := rp
      have ep : 2^(256-r)*2^r=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
      have exp : 256-r  ≤  32 := by omega
      have sm : 2^(256-r)  ≤  2^32 := Nat.pow_le_pow_right (by decide) exp
      let z := SkywalkNat.step^[i] (SkywalkNat.init x ECDSAAdd.p)
      change z.v*2^t=x at hv
      change z.u*2^r+z.v=ECDSAAdd.p at hu
      change z.u+z.v<H   ∨   H  ≤  z.v
      have ucap : z.u<2^32 := by
        have ub : z.u<2^(256-r) := by
          by_contra h
          have mm := Nat.mul_le_mul_right (2^r) (Nat.le_of_not_gt h)
          nlinarith
        omega
      by_cases vb : H  ≤  z.v
      · exact Or.inr vb
      · left
        by_contra ns
        have vl : z.v<H := by omega
        have vt : H<z.v+(2^32+977) := by omega
        have hm : 2^(255-r)*2^r=H := by
          rw [←pow_add]
          change 2^(255-r+r)=(2:Nat)^255
          congr 1
          omega
        have um : z.u<2^(255-r) := by
          by_contra hh
          have mm := Nat.mul_le_mul_right (2^r) (Nat.le_of_not_gt hh)
          nlinarith
        have mm := Nat.mul_le_mul_right (2^r) (show z.u+1  ≤  2^(255-r) by omega)
        nlinarith
end ECDSAAdd.Entrant.TickRanges
namespace ECDSAAdd.Entrant.TickRanges

def Outside (v : Int) : Prop := v< -(H:Int)  ∨  (H:Int) ≤ v

theorem encode_boundary (g s : Bool) (u v : Int) (hu : 0 ≤ u) (hv : 0<v)
    (hvo : v%2=1) (hb : u+v<2*(H:Int)) (gap : u+v<(H:Int)  ∨  (H:Int) ≤ v) :
    let r := SkywalkRails.encode g s u v
    let eo := SkywalkRails.route r.a r.b;
    - (H:Int)  ≤  (SkywalkRails.step r).h  ∧  (SkywalkRails.step r).h<(H:Int)  ∧
      (Outside eo.2 ↔ Outside (SkywalkRails.step r).k) := by
  have hp : 0<(H:Int) := by norm_num [H]
  have ucap : u<(H:Int) := by omega
  by_cases he : u%2=0
  · have step := SkywalkRails.step_encode_even g s u v hu hv hvo he
    have hl : (u+v)%2 ≠ 0 := by omega
    have hn : (-u)%2=0 := by omega
    have hneg : (-u)/2= -(u/2) := by omega
    cases g <;> cases s <;>
      simp only [SkywalkRails.encode,SkywalkRails.route,SkywalkRails.odd,
        SkywalkRails.signed,Bool.false_eq_true,if_false,if_true,hl,hn,he,
        ne_eq,not_false_eq_true,not_true_eq_false,decide_true,decide_false] at step ⊢ <;>
      rw [step] <;> dsimp only <;> unfold Outside <;> omega
  · have step := SkywalkRails.step_encode_odd g s u v hu hv hvo he
    have hl : (u+v)%2=0 := by omega
    have hn : (-u)%2 ≠ 0 := by omega
    cases g <;> cases s <;>
      simp only [SkywalkRails.encode,SkywalkRails.route,SkywalkRails.odd,
        SkywalkRails.signed,Bool.false_eq_true,if_false,if_true,hl,hn,he,
        ne_eq,not_false_eq_true,not_true_eq_false,decide_true,decide_false] at step ⊢ <;>
      rw [step] <;> dsimp only <;> unfold Outside <;> omega
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
theorem run_mid_congr (M X X' E : Program) (m : List Bool) (s : State)
    (hM : measurementCount M = 0) (hc : measurementCount X = measurementCount X')
    (h : ∀ r, run X r (run M [] s) = run X' r (run M [] s)) :
    run (M ++ X ++ E) m s = run (M ++ X' ++ E) m s := by
  rw [List.append_assoc, List.append_assoc, run_append M (X ++ E), run_append M (X' ++ E), hM,
    List.take_zero, List.drop_zero, run_append X E, run_append X' E, hc, h]

theorem run_zero_head (M R : Program) (m : List Bool) (s : State) (hM : measurementCount M = 0) :
    run (M ++ R) m s = run R m (run M [] s) := by
  rw [run_append, hM, List.take_zero, List.drop_zero]

theorem run_congr_head (X X' E : Program) (m : List Bool) (v : State)
    (hc : measurementCount X = measurementCount X') (h : ∀ r, run X r v = run X' r v) :
    run (X ++ E) m v = run (X' ++ E) m v := by
  rw [run_append, run_append X' E, hc, h]

theorem run_head_congr (P P' E : Program) (m : List Bool) (s : State)
    (hP : measurementCount P = 0) (hP' : measurementCount P' = 0)
    (h : run P [] s = run P' [] s) :
    run (P ++ E) m s = run (P' ++ E) m s := by
  rw [run_append P E, run_append P' E, hP, hP', List.take_zero, List.drop_zero, h]

def addCopy : List Wire → List Wire → List Wire → Wire → Program
  | a :: (a' :: as), b :: (b' :: bs), c :: cs, cin =>
      (if as = [] then [.CX cin c] else majority a b cin c) ++
        addCopy (a' :: as) (b' :: bs) cs c ++ eraseCarry a b cin c ++ [.CX a b, .CX cin b]
  | [a], [b], _, cin => [.CX a b, .CX cin b]
  | _, _, _, _ => []

theorem shape_two {x y carry : List Wire} (hy : y.length = 0 + 2) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) :
    ∃ a a' b b' c, x = [a, a'] ∧ y = [b, b'] ∧ carry = [c] := by
  rcases y with _ | ⟨b, _ | ⟨b', _ | ⟨b'', ys⟩⟩⟩ <;> simp at hy
  rcases x with _ | ⟨a, _ | ⟨a', _ | ⟨a'', xs⟩⟩⟩ <;> simp at hx
  rcases carry with _ | ⟨c, _ | ⟨c', cs⟩⟩ <;> simp at hc
  exact ⟨a, a', b, b', c, rfl, rfl, rfl⟩

theorem shape_succ {n : Nat} {x y carry : List Wire} (hy : y.length = n + 1 + 2)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) :
    ∃ a a' a'' as b b' b'' bs c cs, x = a :: a' :: a'' :: as ∧ y = b :: b' :: b'' :: bs ∧
      carry = c :: cs := by
  rcases y with _ | ⟨b, _ | ⟨b', _ | ⟨b'', ys⟩⟩⟩ <;> simp at hy
  rcases x with _ | ⟨a, _ | ⟨a', _ | ⟨a'', xs⟩⟩⟩ <;> simp at hx
  rcases carry with _ | ⟨c, cs⟩ <;> simp at hc
  exact ⟨a, a', a'', xs, b, b', b'', ys, c, cs, rfl, rfl, rfl⟩

theorem regValue_nil' (st : BasisState) : regValue [] st = 0 := rfl

theorem addCopy_counts : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    toffoliCount (addCopy x y carry cin) = n ∧
    measurementCount (addCopy x y carry cin) = n + 1 := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    simp [addCopy, eraseCarry, toffoliCount, measurementCount]
  | succ n ih =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have h := ih (a' :: a'' :: as) (b' :: b'' :: bs) cs c (by simpa using hy)
        (by simpa using hx) (by simpa using hc)
    simp only [addCopy, List.cons_ne_nil, if_false, toffoliCount_append,
        measurementCount_append, h.1, h.2, majority, eraseCarry, toffoliCount, measurementCount]
    omega

theorem regValue_cons' (a : Wire) (r : List Wire) (st : BasisState) :
    regValue (a :: r) st = (st a).toNat + 2 * regValue r st := by
  cases h : st a <;> simp [regValue, h]

theorem copy_affine (A A' B B' C : Bool)
    (hX : A.toNat + 2*A'.toNat < 1 ∨ 3 ≤ A.toNat + 2*A'.toNat)
    (hS : (1 ≤ B.toNat+2*B'.toNat ∧ B.toNat+2*B'.toNat < 3) ↔
      (1 ≤ (A.toNat+2*A'.toNat+(B.toNat+2*B'.toNat)+C.toNat)%4 ∧
      (A.toNat+2*A'.toNat+(B.toNat+2*B'.toNat)+C.toNat)%4 < 3)) :
    carryBit A B C = C := by
  revert hX hS
  cases A <;> cases A' <;> cases B <;> cases B' <;> cases C <;> decide
theorem addCopy_eq : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    (cin :: (x ++ y ++ carry)).Nodup → ∀ (s : State) (m : List Bool),
    (∀ w ∈ carry, s.basis w = false) →
    (regValue x s.basis < 2^n ∨ 3 * 2^n ≤ regValue x s.basis) →
    ((2^n ≤ regValue y s.basis ∧ regValue y s.basis < 3*2^n) ↔
      (2^n ≤ (regValue x s.basis+regValue y s.basis+(s.basis cin).toNat)%2^(n+2) ∧
        (regValue x s.basis+regValue y s.basis+(s.basis cin).toNat)%2^(n+2) < 3*2^n)) →
    run (addCopy x y carry cin) m s = run (addInPlace x y carry cin) m s := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc hnd s m hclean hX hS
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have h4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append, List.count_nil] at this ⊢; omega
    have hbc : b ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hb'c : b' ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hcc : cin ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hzero : s.basis c = false := hclean c (by simp)
    have hK : carryBit (s.basis a) (s.basis b) (s.basis cin) =
        (s.basis cin) := by
      apply copy_affine _ (s.basis a') _ _ _
      · simpa [regValue_cons', regValue_nil'] using hX
      · simpa [regValue_cons', regValue_nil'] using hS
    have hm1 : measurementCount ([.CX cin c] : Program) = 0 := rfl
    have hm2 : measurementCount (majority a b cin c) = 0 := rfl
    have hmid : run ([.CX cin c] : Program) [] s = run (majority a b cin c) [] s := by
      rw [majority_correct _ _ _ _ h4]
      simp only [run]
      apply State.extensionality
      · rfl
      · funext w
        simp only [writeBit, Function.update]
        by_cases hwc : w = c
        · subst hwc
          simp [hbc, hb'c, hcc, hzero, hK]
        · simp [hwc]
    simp only [addCopy, addInPlace, if_pos (rfl : ([] : List Wire) = []), List.append_assoc]
    exact run_head_congr _ _ _ m s hm1 hm2 hmid
  | succ n ih =>
    intro x y carry cin hy hx hc hnd s m hclean hX hS
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have h4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append, List.count_nil] at this ⊢; omega
    have hnd' : (c :: ((a' :: a'' :: as) ++ (b' :: b'' :: bs) ++ cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append] at this ⊢; omega
    have hcx : c ∉ a' :: a'' :: as := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hcy : c ∉ b' :: b'' :: bs := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hccs : c ∉ cs := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hzero : s.basis c = false := hclean c (by simp)
    let A := s.basis a
    let B := s.basis b
    let C := s.basis cin
    let s1 : State := ⟨s.phase, writeBit s.basis c (carryBit A B C)⟩
    have hfirst (record : List Bool) : run (majority a b cin c) record s = s1 := by
      rw [majority_correct _ _ _ _ h4]; simp [s1, hzero, A, B, C]
    have hs1 (w : Wire) (hw : w ≠ c) : s1.basis w = s.basis w := by simp [s1, writeBit, hw]
    have hclean' : ∀ d ∈ cs, s1.basis d = false := by
      intro d hd; rw [hs1 d (fun h => hccs (h ▸ hd))]; exact hclean d (by simp [hd])
    have hxs : regValue (a' :: a'' :: as) s1.basis = regValue (a' :: a'' :: as) s.basis :=
      regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcx (h ▸ hw)))
    have hys : regValue (b' :: b'' :: bs) s1.basis = regValue (b' :: b'' :: bs) s.basis :=
      regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcy (h ▸ hw)))
    have hc1 : s1.basis c = carryBit A B C := by simp [s1, writeBit]
    have hp1 : 2^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
    have hp3 : 2^(n+1+2) = 2 * 2^(n+2) := by rw [show n+1+2 = (n+2)+1 by omega, pow_succ]; ring
    rw [regValue_cons' a, regValue_cons' b] at hS
    rw [regValue_cons' a] at hX
    have step := sum_value_step A B C (regValue (a' :: a'' :: as) s.basis)
      (regValue (b' :: b'' :: bs) s.basis) (n+2)
    have hsb : (sumBit A B C).toNat ≤ 1 := by cases sumBit A B C <;> decide
    have hA : (s.basis a).toNat ≤ 1 := by cases s.basis a <;> decide
    have hX' : regValue (a' :: a'' :: as) s1.basis < 2^n ∨
        3 * 2^n ≤ regValue (a' :: a'' :: as) s1.basis := by
      rw [hxs]; omega
    have hB : (s.basis b).toNat ≤ 1 := by cases s.basis b <;> decide
    have hS' :
        (2^n ≤ regValue (b' :: b'' :: bs) s1.basis ∧
          regValue (b' :: b'' :: bs) s1.basis < 3*2^n) ↔
        (2^n ≤ (regValue (a' :: a'' :: as) s1.basis + regValue (b' :: b'' :: bs) s1.basis +
          (s1.basis c).toNat) % 2^(n+2) ∧
          (regValue (a' :: a'' :: as) s1.basis + regValue (b' :: b'' :: bs) s1.basis +
          (s1.basis c).toNat) % 2^(n+2) < 3*2^n) := by
      rw [hxs,hys,hc1]
      change (sumBit A B C).toNat + 2 * ((regValue (a' :: a'' :: as) s.basis +
        regValue (b' :: b'' :: bs) s.basis + (carryBit A B C).toNat) % 2^(n+2)) =
        ((A.toNat + 2 * regValue (a' :: a'' :: as) s.basis) +
          (B.toNat + 2 * regValue (b' :: b'' :: bs) s.basis) + C.toNat) % 2^(n+2+1) at step
      rw [show n+2+1 = n+1+2 by omega] at step
      generalize (regValue (a' :: a'' :: as) s.basis + regValue (b' :: b'' :: bs) s.basis +
        (carryBit A B C).toNat) % 2^(n+2) = S' at step ⊢
      generalize ((A.toNat + 2 * regValue (a' :: a'' :: as) s.basis) +
        (B.toNat + 2 * regValue (b' :: b'' :: bs) s.basis) + C.toNat) % 2^(n+1+2) = S at step hS
      omega
    have hmc : measurementCount (addCopy (a' :: a'' :: as) (b' :: b'' :: bs) cs c) =
        measurementCount (addInPlace (a' :: a'' :: as) (b' :: b'' :: bs) cs c) := by
      rw [(addCopy_counts n _ _ _ c (by simpa using hy) (by simpa using hx)
          (by simpa using hc)).2,
        (addInPlace_counts _ _ _ c (by simpa using hx) (by simpa using hc)).2]
      simp only [List.length_cons] at hy ⊢
      omega
    have hm0 : measurementCount (majority a b cin c) = 0 := rfl
    simp only [addCopy, addInPlace, List.cons_ne_nil, if_false]
    rw [List.append_assoc (majority a b cin c ++ _), List.append_assoc (majority a b cin c ++ _)]
    apply run_mid_congr _ _ _ _ m s hm0 hmc
    intro record
    rw [hfirst]
    exact ih _ _ _ c (by simpa using hy) (by simpa using hx) (by simpa using hc) hnd' s1 record
      hclean' hX' hS'

end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
def signedAddCopy (q : Wire) (x y carry : List Wire) : Program :=
  signComplement q x ++ addCopy x y carry q ++ signComplement q x

def Shape (n V : Nat) : Prop := V < 2^n ∨ 3*2^n ≤ V
def Band (n V : Nat) : Prop := 2^n ≤ V ∧ V<3*2^n

theorem shape_complement (n V : Nat) (hv : V < 2^(n+2)) (h : Shape n V) :
    Shape n (2^(n+2)-1-V) := by
  have pow : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  unfold Shape at *
  omega

theorem shape_of_signed (n V : Nat) (hv : V < 2^(n+2))
    (lo : -((2^n:Nat):Int) ≤ signedDecode (n+2) V)
    (hi : signedDecode (n+2) V < ((2^n:Nat):Int)) : Shape n V := by
  have p2 : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  have p1 : 2^(n+2-1) = 2*2^n := by rw [show n+2-1=n+1 by omega,pow_succ]; ring
  unfold signedDecode at lo hi
  split_ifs at lo hi <;> unfold Shape <;> omega

theorem signedAddCopy_eq (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (clean : ∀ w ∈ cs, s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Band n (regValue y s.basis) ↔ Band n (regValue y (run (signedAdd q x y cs) [] s).basis)) :
    run (signedAddCopy q x y cs) m s=run (signedAdd q x y cs) m s := by
  have hxnd : x.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1).1
  have qx : q∉x := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have dis : List.Disjoint x (y++cs) := by
    have h : (x++(y++cs)).Nodup := by simpa only [List.append_assoc] using (List.nodup_cons.mp hn).2
    exact (List.nodup_append'.mp h).2.2
  have zx := (signComplement_counts q x).2
  let u := run (signComplement q x) [] s
  have fan := signComplement_correct q x hxnd qx s []
  have ux : Shape n (regValue x u.basis) := by
    change Shape n (regValue x (run (signComplement q x) [] s).basis)
    rw [fan.2.2]
    cases hs : s.basis q
    · exact source
    · simpa only [hx,if_true] using shape_complement n _ (by simpa [hx] using regValue_lt x s.basis) source
  have clean' : ∀ w ∈ cs, u.basis w=false := by
    intro w hw
    exact (fan.2.1 w (fun h => List.disjoint_left.mp dis h (List.mem_append_right _ hw))).trans (clean w hw)
  have out (r : List Bool) :
      regValue y (run (signComplement q x) r (run (addInPlace x y cs q) r u)).basis =
      regValue y (run (addInPlace x y cs q) r u).basis := by
    have h := signComplement_correct q x hxnd qx (run (addInPlace x y cs q) r u) r
    apply regValue_congr
    intro w hw
    exact h.2.1 w (fun hxw => List.disjoint_left.mp dis hxw (List.mem_append_left _ hw))
  have old : regValue y (run (signedAdd q x y cs) [] s).basis =
      regValue y (run (addInPlace x y cs q) [] u).basis := by
    simp only [signedAdd,List.append_assoc]
    rw [run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  have add := addInPlace_correct x y cs q hn (hx.trans hy.symm) hc u [] clean'
  have uy : regValue y u.basis=regValue y s.basis := by
    exact regValue_congr _ _ _ (fun w hw => fan.2.1 w
      (fun hxw => List.disjoint_left.mp dis hxw (List.mem_append_left _ hw)))
  have us : Band n (regValue y u.basis) ↔
      Band n ((regValue x u.basis+regValue y u.basis+(u.basis q).toNat)%2^(n+2)) := by
    rw [←uy,old,add.2.2,hy] at sum
    exact sum
  have eq (r : List Bool) := addCopy_eq n x y cs q hy (hx.trans hy.symm)
    hc hn u r clean' ux us
  simp only [signedAddCopy,signedAdd,List.append_assoc]
  rw [run_zero_head _ _ m s zx,run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq]
  have mc := addCopy_counts n x y cs q hy (hx.trans hy.symm) hc
  have mo := addInPlace_counts x y cs q (hx.trans hy.symm) hc
  rw [mc.2,mo.2,hy]
  rfl
def recordCopy (sx sy q : Wire) (x y cs : List Wire) : Program :=
  skywalkSignToggle sx sy q ++ signedAddCopy q x y cs ++ skywalkSignToggle sx sy q

theorem signedAddCopy_counts (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length) :
    toffoliCount (signedAddCopy q x y cs)=n ∧ measurementCount (signedAddCopy q x y cs)=n+1 := by
  have h := addCopy_counts n x y cs q hy (hx.trans hy.symm) hc
  simp only [signedAddCopy,toffoliCount_append,measurementCount_append,
    (signComplement_counts q x).1,(signComplement_counts q x).2,h.1,h.2]
  exact ⟨by omega,by omega⟩

theorem toggle_frame (sx sy q : Wire) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (w : Wire) (hw : w≠q) :
    (run (skywalkSignToggle sx sy q) m s).basis w=s.basis w := by
  rw [skywalkSignToggle_correct sx sy q hqx hqy]
  simp [writeBit,hw]

theorem recordCopy_eq (n : Nat) (sx sy q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (clean : ∀w∈cs,s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Band n (regValue y s.basis) ↔ Band n (regValue y (run (signedRecord sx sy q x y cs) [] s).basis)) :
    run (recordCopy sx sy q x y cs) m s=run (signedRecord sx sy q x y cs) m s := by
  have qrest := (List.nodup_cons.mp hn).1
  have away (w : Wire) (hw : w∈x++y++cs) : w≠q := by
    intro he; subst w; exact qrest hw
  let u := run (skywalkSignToggle sx sy q) [] s
  have ut (w : Wire) (hw : w≠q) : u.basis w=s.basis w := toggle_frame sx sy q hqx hqy s [] w hw
  have ux : regValue x u.basis=regValue x s.basis :=
    regValue_congr _ _ _ (fun w hw => ut w (away w (by simp [hw])))
  have uc : ∀w∈cs,u.basis w=false := by
    intro w hw
    exact (ut w (away w (by simp [hw]))).trans (clean w hw)
  have zx := (skywalkSignToggle_counts sx sy q).2
  have out (r : List Bool) :
      regValue y (run (skywalkSignToggle sx sy q) r (run (signedAdd q x y cs) r u)).basis =
      regValue y (run (signedAdd q x y cs) r u).basis :=
    regValue_congr _ _ _ (fun w hw => toggle_frame sx sy q hqx hqy _ r w (away w (by simp [hw])))
  have old : regValue y (run (signedRecord sx sy q x y cs) [] s).basis =
      regValue y (run (signedAdd q x y cs) [] u).basis := by
    simp only [signedRecord,List.append_assoc]
    rw [run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  have uy : regValue y u.basis=regValue y s.basis :=
    regValue_congr _ _ _ (fun w hw => ut w (away w (by simp [hw])))
  rw [←uy,old] at sum
  have eq (r : List Bool) := signedAddCopy_eq n q x y cs hx hy hc hn u r uc (ux ▸ source) sum
  have mc := (signedAddCopy_counts n q x y cs hx hy hc).2
  have mo := (signedWord_counts q x y cs (hx.trans hy.symm) hc).2.1
  simp only [recordCopy,signedRecord,List.append_assoc]
  rw [run_zero_head _ _ m s zx,run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq,mc,mo,hy]
  rfl
def narrowCopy (L : NarrowSignedRecordLayout) (n : Nat) : Program :=
  recordCopy L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1)) ++
    signComplement L.q (L.y.drop n)

theorem record_source (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0) :
    regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) m s).basis = regValue L.xp s.basis := by
  have h := signedRecord_spec L.xlo L.ylo L.sx L.sy L.q L.carryLow (L.short_nodup hn)
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
    (signedRegValue L.xp s.basis) (signedRegValue L.yp s.basis) s m ⟨hq,rfl,rfl,clean⟩
  have eq := (signedRegValue_eq_iff L.xp _ _).mp h.2.2.1
  exact regValue_congr _ _ _ eq

theorem narrowCopy_eq (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) (s : State) (m : List Bool)
    (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0)
    (source : Shape n (regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis))
    (sum : Band n (regValue L.yp s.basis) ↔ Band n (regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis)) :
    run (narrowCopy L (n+2)) m s=run (narrowSignedRecord L (n+2)) m s := by
  have views := L.views (n+2) hw
  have clean' : ∀w∈L.carryLow,s.basis w=false := (regValue_zero _ _).mp clean
  have qx : L.sx≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have fan (r : List Wire) (hr : ∀w∈r,w∉L.yhigh) (v : State) (record : List Bool) :
      regValue r (run (signComplement L.q L.yhigh) record v).basis=regValue r v.basis := by
    have f := signComplement_correct L.q L.yhigh (L.high_nodup hn) (L.q_high hn) v record
    exact regValue_congr _ _ _ (fun w hw => f.2.1 w (hr w hw))
  have xaway : ∀w∈L.xp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp only [NarrowSignedRecordLayout.x,List.mem_append] at *; tauto)
  have yaway : ∀w∈L.yp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp [hw'])
  have outx : regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.xp xaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  have outy : regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.yp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.yp yaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  rw [outx,record_source L (n+2) hw hn s [] hq clean] at source
  rw [outy] at sum
  have eq (r : List Bool) := recordCopy_eq n L.sx L.sy L.q L.xp L.yp L.carryLow
    hw.x hw.y (hw.carry.trans hw.y.symm) (L.short_nodup hn) qx qy s r clean' source sum
  have mc := signedAddCopy_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have rz := (skywalkSignToggle_counts L.sx L.sy L.q).2
  have old := (signedWord_counts L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)).2.1
  have counts : measurementCount (recordCopy L.sx L.sy L.q L.xp L.yp L.carryLow)=
      measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) := by
    simp only [recordCopy,signedRecord,measurementCount_append,rz,mc.2,old,hw.y]
    omega
  simp only [narrowCopy,narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
  rw [run_append,run_append,run_take,run_take,eq,counts]
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic Baselines Challenge RecordedQuantum
theorem addCopy_wires (x y carry : List Wire) (cin : Wire) :
    wires (addCopy x y carry cin) ⊆ (cin :: (x ++ y ++ carry)).toFinset := by
  induction x generalizing y carry cin with
  | nil => simp [addCopy, wires]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [addCopy, wires]
      | cons b bs =>
        cases bs with
        | nil =>
          intro w hw
          simp only [addCopy, wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, Finset.notMem_empty, or_false] at hw
          simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
          tauto
        | cons b' bs => simp [addCopy, wires]
    | cons a' as =>
      cases y with
      | nil => simp [addCopy, wires]
      | cons b bs =>
        cases bs with
        | nil => simp [addCopy, wires]
        | cons b' bs =>
          cases carry with
          | nil => simp [addCopy, wires]
          | cons c cs =>
            have hr := ih (b' :: bs) cs c
            have hm : wires (majority a b cin c) = {a, b, cin, c} := by
              ext w; simp [majority, wires, Instr.wires]; tauto
            have he := eraseCarry_wires a b cin c
            intro w hw
            simp only [addCopy, wires_append, Finset.mem_union, he] at hw
            simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
            rcases hw with ((h | h) | h) | h
            · split_ifs at h
              · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
                  Finset.mem_singleton, Finset.notMem_empty, or_false] at h
                tauto
              · rw [hm] at h
                simp only [Finset.mem_insert, Finset.mem_singleton] at h
                tauto
            · have := hr h
              simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at this
              tauto
            · simp only [Finset.mem_insert, Finset.mem_singleton] at h
              tauto
            · simp only [wires, Instr.wires, Finset.mem_union, Finset.mem_insert,
                Finset.mem_singleton, Finset.notMem_empty, or_false] at h
              tauto

theorem addCopy_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: x ++ y ++ carry).Nodup) : GatePhysical (addCopy x y carry cin) := by
  induction x generalizing y carry cin with
  | nil => simp [addCopy, GatePhysical]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases y with
      | nil => simp [addCopy, GatePhysical]
      | cons b ys =>
        cases ys with
        | cons b' ys => simp [addCopy, GatePhysical]
        | nil =>
          have hab : a ≠ b := by
            intro e; subst b
            have h := List.nodup_iff_count.mp hn a
            simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at h
            omega
          have hcb : cin ≠ b := by
            intro e; subst cin
            have h := List.nodup_iff_count.mp hn b
            simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at h
            omega
          simp [addCopy, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hab, hcb]
    | cons a' xs =>
      cases y with
      | nil => simp [addCopy, GatePhysical]
      | cons b ys =>
        cases ys with
        | nil => simp [addCopy, GatePhysical]
        | cons b' ys =>
          cases carry with
          | nil => simp [addCopy, GatePhysical]
          | cons k ks =>
            have hs : [a,b,cin,k,b'].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons, List.count_append, List.count_nil] at h ⊢; omega
            have ht : (k :: (a'::xs) ++ (b'::ys) ++ ks).Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons, List.count_append] at h ⊢; omega
            have hs4 : [a,b,cin,k].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hs q
              simp only [List.count_cons, List.count_nil] at h ⊢; omega
            have htail := ih (b'::ys) ks k ht
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
              not_or, not_false_eq_true, and_true] at hs
            rw [addCopy]
            simp only [gatePhysical_append]
            refine ⟨⟨⟨?_, htail⟩, eraseCarry_physical _ _ _ _⟩, ?_⟩
            · split_ifs
              · simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hs.2.1.2.1, hs.2.2.1.1,
                  Ne.symm hs.2.2.2]
              · exact majority_physical _ _ _ _ hs4
            · have hcb : cin ≠ b := Ne.symm hs.2.1.1
              simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hs.1.1, hcb]

theorem signedAddCopy_support (q : Wire) (x y cs : List Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    wires (signedAddCopy q x y cs) ⊆ wires (signedAdd q x y cs) := by
  rw [(signedWord_wires q x y cs hx hc).1]
  have fan : wires (signComplement q x) ⊆ (q::(x++y++cs)).toFinset := by
    intro w hw
    have h := signComplement_wires_subset q x hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  simp only [signedAddCopy,wires_append,Finset.union_subset_iff]
  exact ⟨⟨fan,addCopy_wires x y cs q⟩,fan⟩

theorem narrowCopy_counts (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    toffoliCount (narrowCopy L (n+2))+1=toffoliCount (narrowSignedRecord L (n+2)) ∧
      measurementCount (narrowCopy L (n+2))=measurementCount (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have h := signedAddCopy_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have old := narrowSignedRecord_counts L (n+2) hw
  have z := skywalkSignToggle_counts L.sx L.sy L.q
  have f := signComplement_counts L.q L.yhigh
  simp only [narrowCopy,recordCopy,v.1,v.2.1,v.2.2.1,v.2.2.2,
    toffoliCount_append,measurementCount_append,z.1,z.2,h.1,h.2,f.1,f.2,old.1,old.2.1]
  exact ⟨by omega,by omega⟩

theorem narrowCopy_support (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    wires (narrowCopy L (n+2)) ⊆ wires (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have sub := signedAddCopy_support L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  simp only [narrowCopy,narrowSignedRecord,recordCopy,signedRecord,v.1,v.2.1,v.2.2.1,v.2.2.2,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) sub)
    (Finset.Subset.refl _)) (Finset.Subset.refl _)

theorem signedAddCopy_physical (q : Wire) (x y cs : List Wire) (hn : (q::(x++y++cs)).Nodup) :
    GatePhysical (signedAddCopy q x y cs) := by
  have qx : q∉x := fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
  have fan := signComplement_physical q x qx
  have top := addCopy_physical x y cs q hn
  simp only [signedAddCopy,gatePhysical_append]
  exact ⟨⟨fan,top⟩,fan⟩

theorem narrowCopy_physical (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) : GatePhysical (narrowCopy L (n+2)) := by
  have v := L.views (n+2) hw
  have nd := L.short_nodup hn
  have qx : L.sx≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have toggle : GatePhysical (skywalkSignToggle L.sx L.sy L.q) := by
    simp [skywalkSignToggle,GatePhysical,PhysicalInstr,ProperGate,qx,qy]
  have top := signedAddCopy_physical L.q L.xp L.yp L.carryLow nd
  have fan := signComplement_physical L.q L.yhigh (L.q_high hn)
  simp only [narrowCopy,recordCopy,v.1,v.2.1,v.2.2.1,v.2.2.2,gatePhysical_append]
  exact ⟨⟨⟨toggle,top⟩,toggle⟩,fan⟩

theorem top_slots_le_old (x y cs : List Wire) (c : Wire) :
    gateSlots (addCopy x y cs c) ≤ gateSlots (addInPlace x y cs c) := by
  induction x generalizing y cs c with
  | nil => simp [addCopy,addInPlace]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [addCopy,addInPlace]
      | cons b bs => cases bs <;> simp [addCopy,addInPlace]
    | cons a' as =>
      cases y with
      | nil => simp [addCopy,addInPlace]
      | cons b bs =>
        cases bs with
        | nil => simp [addCopy,addInPlace]
        | cons b' bs =>
          cases cs with
          | nil => simp [addCopy,addInPlace]
          | cons d ds =>
            have h := ih (b'::bs) ds d
            simp only [addCopy,addInPlace,gateSlots_append] at h ⊢
            split_ifs <;> simp only [majority_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots] at h ⊢ <;> omega

theorem narrowCopy_slots (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    gateSlots (narrowCopy L (n+2)) ≤ gateSlots (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have top := top_slots_le_old L.xp L.yp L.carryLow L.q
  simp only [narrowCopy,narrowSignedRecord,recordCopy,signedRecord,signedAddCopy,signedAdd,
    v.1,v.2.1,v.2.2.1,v.2.2.2,gateSlots_append]
  omega
end ECDSAAdd.Entrant.TickRanges
end

section
set_option exponentiation.threshold 512
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
def head (w : Nat → Wire) (i : Nat) : Program :=
  let L := W.compactSkywalkTickLayout w i
  (if i=224 ∨ (256 ≤ i  ∧  i ≤ 509) then W.repairedRoute L
    else skywalkRoute L.a0 L.b0 L.ah L.bh) ++ skywalkSignedHalf L.aSign L.ext

def tail (w : Nat → Wire) (i : Nat) : Program :=
  [.CX (W.compactSkywalkTickLayout w i).previous (W.compactSkywalkTickLayout w i).a0] ++
    W.compactSkywalkTickCleanup w i

def tick (w : Nat → Wire) (i : Nat) : Program :=
  if 225 ≤ i ∧ i ≤ 254 then
    head w i ++ narrowCopy (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
      (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i
  else TickGap.tick w i

theorem old_split (w : Nat → Wire) (i : Nat) (band : 225 ≤ i  ∧  i ≤ 254) :
    W.repairedTick w i = head w i ++
      narrowSignedRecord (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
        (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i := by
  have nf : ¬ W.fwdTrim i := by unfold W.fwdTrim; omega
  simp only [W.repairedTick,if_neg nf,W.repairedTick0,head,tail,W.compactSkywalkTick,narrowSkywalkTick]
  split_ifs  <;> simp only [List.append_assoc]

theorem repairedRoute_small_support (L : SkywalkIntegerLayout) (hv : L.Valid) (hpos : 0 < L.bMid.length) :
    wires (W.repairedRoute L) ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
  have lo := swapRegisters_wires L.a0 L.aMid L.bMid hv.mids
  have tm : L.bMid.getD (L.bMid.length-1) 0∈L.bMid := W.repair_member_getD _ _ (by omega)
  have ls : wires (swapRegisters L.a0 L.aMid L.bMid) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    have h := lo hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh] at h ⊢
    tauto
  have ss : wires (W.signRepair L.aSign L.bSign L.previous (L.bMid.getD (L.bMid.length-1) 0)) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [W.signRepair,wires,Instr.wires,correctionWires,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh,
      List.not_mem_nil,or_false]
    have ht : q=L.bMid.getD (L.bMid.length-1) 0 → q∈L.bMid := fun he => he ▸ tm
    tauto
  have cx : wires [.CX L.a0 L.b0] ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  simp only [W.repairedRoute,W.repairedSwap,wires_append,Finset.union_subset_iff]
  exact ⟨⟨ls,ss⟩,cx⟩

theorem head_aux (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).history::(W.compactSkywalkTickLayout w i).carry) :
    (run (head w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have hpos : 0 < L.bMid.length := by
    change 0 < (wireBlock w 771 (W.compactSkywalkTickPreWidth i-2)).length
    rw [wireBlock_length]
    have width := W.compactSkywalkTick_width_bounds i hi
    omega
  have dis : List.Disjoint (L.history::L.carry) (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)) := by
    have nd : ((L.history::L.carry)++(L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh))).Nodup := by
      apply List.nodup_iff_count.mpr
      intro a
      have h := List.nodup_iff_count.mp hv.nodup a
      simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at h ⊢
      omega
    exact (List.nodup_append'.mp nd).2.2
  have qaway : q∉L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh) := List.disjoint_left.mp dis hq
  have sup : wires (head w i) ⊆ (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    have inc : (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [List.mem_toFinset,List.mem_cons] at ha ⊢
      tauto
    have repair := (repairedRoute_small_support L hv hpos).trans inc
    have full : wires (skywalkRoute L.a0 L.b0 L.ah L.bh) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      have h := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
      tauto
    have half : wires (skywalkSignedHalf L.aSign L.ext) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [skywalkSignedHalf,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.notMem_empty,or_false] at ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,List.mem_singleton]
      tauto
    simp only [head,wires_append,Finset.union_subset_iff]
    split_ifs  <;> exact ⟨by assumption,half⟩
  exact run_preserves_outside _ _ _ _ (fun h => qaway (List.mem_toFinset.mp (sup h)))

theorem tail_prefix (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).half.take (W.compactSkywalkTickPostWidth i) ++
      (W.compactSkywalkTickLayout w i).b.take (W.compactSkywalkTickPostWidth i)) :
    (run (tail w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have words := W.compactSkywalkTick_words_disjoint w i hi hn
  have nd := (List.nodup_cons.mp (L.record_nodup hv)).2
  have wa : L.half.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).1
  have wb : L.b.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.1
  have adot : List.Disjoint (L.half.take n) (L.half.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wa
  have bdot : List.Disjoint (L.b.take n) (L.b.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wb
  have apart : q∉L.half.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact List.disjoint_left.mp adot hqa
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_drop h) (List.mem_of_mem_take hqb)
  have bpart : q∉L.b.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_take hqa) (List.mem_of_mem_drop h)
    · exact List.disjoint_left.mp bdot hqb
  have q0 : q≠L.a0 := by
    have qm : q∈L.half++L.b := by
      rcases List.mem_append.mp hq with hqa|hqb
      · exact List.mem_append_left _ (List.mem_of_mem_take hqa)
      · exact List.mem_append_right _ (List.mem_of_mem_take hqb)
    intro he
    subst q
    have h := List.nodup_iff_count.mp hv.nodup L.a0
    have hq' := List.count_pos_iff.mpr qm
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,List.count_nil,List.count_cons,List.count_append,
      List.count_singleton] at h hq'
    simp only [beq_self_eq_true,if_true] at h
    omega
  have valid := W.compactSkywalkTick_release_valid w i hi hn
  have af (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickARelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.1 v r).2.1 q apart
  have bf (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickBRelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.2 v r).2.1 q bpart
  simp only [tail,W.compactSkywalkTickCleanup,run_append,run_take]
  rw [bf,af]
  change Function.update s.basis L.a0 (s.basis L.a0 ^^ s.basis L.previous) q = s.basis q
  exact Function.update_of_ne q0 _ _
theorem route_aux_frame (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈L.previous::L.history::L.ext::L.carry) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis q=s.basis q := by
  have hn : ((L.previous::L.history::L.ext::L.carry)++
      (L.a0::L.b0::(L.ah++L.bh))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hv.nodup w
    simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  apply run_preserves_outside
  intro hm
  have hh := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) hm
  exact List.disjoint_left.mp hd hq (List.mem_toFinset.mp hh)

theorem route_int_values (L : SkywalkIntegerLayout) (hv : L.Valid) (A B : Int)
    (hp : (A+B)%2=1) (s : State) (m : List Bool)
    (ha : signedRegValue L.a s.basis=A) (hb : signedRegValue L.b s.basis=B)
    (hext : s.basis L.ext=false) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).phase=s.phase ∧
    signedRegValue (L.ext::L.ah) (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).1 ∧
    signedRegValue L.b (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).2 ∧
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis L.a0=SkywalkRails.odd A := by
  have hna : L.ah≠[] := by simp [SkywalkIntegerLayout.ah]
  have hnb : L.bh≠[] := by simp [SkywalkIntegerLayout.bh]
  have hA := ha.symm.trans (signedRegValue_cons L.a0 L.ah s.basis hna)
  have hB := hb.symm.trans (signedRegValue_cons L.b0 L.bh s.basis hnb)
  have hpar : s.basis L.b0=(!s.basis L.a0) := by
    cases hca : s.basis L.a0 with
    | false =>
      cases hcb : s.basis L.b0 with
      | false =>
        simp [hca,hcb] at hA hB
        omega
      | true => rfl
    | true =>
      cases hcb : s.basis L.b0 with
      | false => rfl
      | true =>
        simp [hca,hcb] at hA hB
        omega
  have hctrl : s.basis L.a0=SkywalkRails.odd A := by
    cases hc : s.basis L.a0 with
    | false =>
      have he : A%2=0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
    | true =>
      have he : A%2≠0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s
  obtain ⟨hf,_,hctl,hlo,hrawA,hrawB⟩ := skywalkRoute_correct L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv) s m hpar
  have he0 : t.basis L.ext=false :=
    (route_aux_frame L hv s m L.ext (by simp)).trans hext
  have hsa : signedRegValue L.ah t.basis=
      if s.basis L.a0 then signedRegValue L.bh s.basis else signedRegValue L.ah s.basis := by
    have hh := congrArg (signedDecode L.ah.length) hrawA
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  have hsb : signedRegValue L.bh t.basis=
      if s.basis L.a0 then signedRegValue L.ah s.basis else signedRegValue L.bh s.basis := by
    have hh := congrArg (signedDecode L.bh.length) hrawB
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  refine ⟨hf,?_,?_,hctl.trans hctrl⟩
  · rw [signedRegValue_cons L.ext L.ah t.basis hna,he0,hsa]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega

  · change signedRegValue (L.b0::L.bh) t.basis=_
    rw [signedRegValue_cons L.b0 L.bh t.basis hnb,hlo,hsb]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega


theorem head_odd_value (L : SkywalkIntegerLayout) (hv : L.Valid) (A B : Int)
    (par : (A+B)%2=1) (s : State) (m : List Bool)
    (ha : signedRegValue L.a s.basis=A) (hb : signedRegValue L.b s.basis=B)
    (he : s.basis L.ext=false) :
    signedRegValue L.b (run (skywalkRoute L.a0 L.b0 L.ah L.bh ++
      skywalkSignedHalf L.aSign L.ext) m s).basis=(SkywalkRails.route A B).2 := by
  have route := (route_int_values L hv A B par s [] ha hb he).2.2.1
  have zero := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh (L.high_lengths hv) (L.route_nodup hv)).2
  rw [run_append,zero,List.take_zero,List.drop_zero]
  have extaway (q : Wire) (hq : q∈L.b) : q≠L.ext := by
    intro hh
    subst q
    have cnt := List.nodup_iff_count.mp hv.nodup L.ext
    have mem := List.count_pos_iff.mpr hq
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.b,List.count_cons,List.count_append,
      List.count_nil,List.count_singleton,beq_self_eq_true,if_true] at cnt mem
    omega
  apply Eq.trans (show signedRegValue L.b _=signedRegValue L.b
      (run (skywalkRoute L.a0 L.b0 L.ah L.bh) [] s).basis from ?_) route
  unfold signedRegValue
  congr 1
  exact regValue_congr _ _ _ (fun q hq =>
    (skywalkSignedHalf_frame L.aSign L.ext _ m).2 q (extaway q hq))

theorem band_signed (n V : Nat) (hv : V<2^(n+2)) :
    Band n V ↔ signedDecode (n+2) V< -((2^n:Nat):Int) ∨
      ((2^n:Nat):Int)≤signedDecode (n+2) V := by
  have p2 : 2^(n+2)=4*2^n := by rw [pow_add]; norm_num; ring
  have p1 : 2^(n+2-1)=2*2^n := by rw [show n+2-1=n+1 by omega,pow_succ]; ring
  unfold Band signedDecode
  split_ifs <;> omega

theorem repaired_output_info (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x i : Nat) (hx0 : 0<x) (hx : x<p) (cop : x.Coprime p)
    (band : 225 ≤ i ∧ i ≤ 254) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    Shape (n-2) (regValue (L.half.take n) (run (W.repairedTick w i) m s).basis) ∧
      (Band (n-2) (regValue (L.b.take n) (run (head w i) m s).basis) ↔
        Band (n-2) (regValue (L.b.take n) (run (W.repairedTick w i) m s).basis)) := by
  dsimp only
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  have hi : i<512 := by omega
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
  let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
  have valid := SkywalkNat.iter_valid i (SkywalkNat.init x p) hp0 hpo
  have cap := W.iter_sum_late x p i hx0 hpo hp gap hx (by omega)
  have early := early_gap x i hx0 hx band
  obtain ⟨G,S,enc⟩ := SkywalkTrace.iter_encoded i false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at enc
  change r=SkywalkRails.encode G S (z.u:Int) (z.v:Int) at enc
  have u0 : 0 ≤ (z.u:Int) := by omega
  have v0 : 0 < (z.v:Int) := by exact_mod_cast valid.1
  have vo : (z.v:Int)%2=1 := by exact_mod_cast valid.2.1
  have cp : (z.u:Int)+(z.v:Int)<2*(H:Int) := by
    change z.u+z.v<2^256 at cap
    have : 2^256=2*H := by norm_num [H]
    exact_mod_cast (this ▸ cap)
  have eg : (z.u:Int)+(z.v:Int)<(H:Int) ∨ (H:Int) ≤ (z.v:Int) := by
    change z.u+z.v<H ∨ H≤z.v at early
    exact_mod_cast early
  have bounds := encode_boundary G S (z.u:Int) (z.v:Int) u0 v0 vo cp eg
  rw [←enc] at bounds
  have par : (r.a+r.b)%2=1 := by rw [enc]; exact SkywalkRails.encode_odd_sum G S _ _ vo
  have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp gap hx cop hi s hs
  have fit := W.narrowSkywalk_iter_fit x p i hp0 hx0 hpo hp gap hx cop hi
  have out := W.compactSkywalkTickOutput_spec w i hi hn _ _ _ fit.1 fit.2.1 fit.2.2.1 fit.2.2.2.1 fit.2.2.2.2 s [] input
  have nw : n=257 := by unfold n W.compactSkywalkTickPostWidth W.narrowSkywalkWidth; omega
  have lenA : n ≤ L.half.length := by
    rw [W.compactSkywalkTick_half w i hi,wireBlock_length]
    exact (W.compactSkywalkTick_width_bounds i hi).2.2.1
  have lenB : L.b.length=n := by
    rw [W.compactSkywalkTick_b w i hi,wireBlock_length]
    unfold n W.compactSkywalkTickPostWidth W.compactSkywalkTickPreWidth
      W.narrowSkywalkRouteWidth W.narrowSkywalkWidth
    omega
  have av : (W.compactSkywalkTickARelease w i).retained=L.half.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) lenA
  have bv : (W.compactSkywalkTickBRelease w i).retained=L.b.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) (by change n ≤ L.b.length; omega)
  have a := out.2.1
  have b := out.2.2.1
  rw [av] at a
  rw [bv] at b
  have lenA' : (L.half.take n).length=n := by simp [List.length_take,Nat.min_eq_left lenA]
  have lenB' : (L.b.take n).length=n := by simp [List.length_take,lenB]
  have old : run (W.repairedTick w i) m s=run (W.compactSkywalkTick w i) [] s :=
    W.repairedTick_eq w hn x p i hp0 hx0 hpo hp gap hx cop hi s m hs
  have valO : signedRegValue (L.b.take n) (run (head w i) m s).basis=
      (SkywalkRails.route r.a r.b).2 := by
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have he : ¬(i=224 ∨ (256 ≤ i ∧ i ≤ 509)) := by omega
    change signedRegValue _ (run _ m s).basis=_
    rw [head,if_neg he,List.take_of_length_le (by omega : L.b.length≤n)]
    exact head_odd_value L hv r.a r.b par s m input.1 input.2.1 input.2.2.2.1
  have rawShape : Shape (n-2) (regValue (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis) := by
    unfold signedRegValue at a
    rw [lenA'] at a
    rw [nw] at a ⊢
    apply shape_of_signed 255 _ (by have h := regValue_lt (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis; rw [lenA',nw] at h; exact h)
    · rw [a]; exact bounds.1
    · rw [a]; exact bounds.2.1
  refine ⟨old ▸ rawShape,?_⟩
  rw [old]
  have oy : Band (n-2) (regValue (L.b.take n) (run (head w i) m s).basis) ↔
      Outside (SkywalkRails.route r.a r.b).2 := by
    have hh := band_signed 255 (regValue (L.b.take n) (run (head w i) m s).basis)
      (by have h := regValue_lt (L.b.take n) (run (head w i) m s).basis; rw [lenB',nw] at h; simpa only [nw] using h)
    unfold signedRegValue at valO
    rw [lenB',nw] at valO
    simpa only [nw,Nat.reduceSub,valO,Outside,H] using hh
  have ky : Band (n-2) (regValue (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis) ↔
      Outside (SkywalkRails.step r).k := by
    have hh := band_signed 255 (regValue (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis)
      (by have h := regValue_lt (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis; rw [lenB',nw] at h; simpa only [nw] using h)
    unfold signedRegValue at b
    rw [lenB',nw] at b
    simpa only [nw,Nat.reduceSub,b,Outside,H] using hh
  exact oy.trans (bounds.2.2.trans ky.symm)
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic
theorem tick_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x i : Nat) (hx0 : 0 < x) (hx : x < p) (cop : x.Coprime p) (hi : i < 512)
    (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (tick w i) m s=run (W.repairedTick w i) m s := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    let P := head w i
    let Q := narrowSignedRecord R n
    let E := tail w i
    let u := run P (m.take (measurementCount P)) s
    let v := run Q (m.drop (measurementCount P)) u
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have width := W.compactSkywalkTick_width_bounds i hi
    have npos : 2 ≤ n := width.2.1
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have nd : R.wires.Nodup := narrowSkywalkRecord_nodup L hv n (by omega) nlen
    have n2 : n-2+2=n := by omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have whole : run (W.repairedTick w i) m s=
        run E ((m.drop (measurementCount P)).drop (measurementCount Q)) v := by
      rw [old_split _ _ band,List.append_assoc,run_append,run_take,run_append,run_take]
      simp only [P,Q,E,u,v,run_take]
      rfl
    have sizes := repaired_output_info w hn x i hx0 hx cop band s m hs
    have keep (r : List Wire) (hr : r⊆L.half.take n++L.b.take n) :
        regValue r (run (W.repairedTick w i) m s).basis=regValue r v.basis := by
      rw [whole]
      apply regValue_congr
      intro q hq
      exact tail_prefix w i hi hn v _ q (hr hq)
    have shapeX : Shape (n-2) (regValue (L.half.take n) v.basis) := by
      rw [←keep _ (by intro q hq; exact List.mem_append_left _ hq)]
      exact sizes.1
    have bandY : Band (n-2) (regValue (L.b.take n) u.basis) ↔
        Band (n-2) (regValue (L.b.take n) v.basis) := by
      have yu : run (head w i) m s=u := by dsimp only [u,P]; rw [run_take]
      have yv := keep (L.b.take n) (by intro q hq; exact List.mem_append_right _ hq)
      have sy : Band (n-2) (regValue (L.b.take n) (run (head w i) m s).basis) ↔
          Band (n-2) (regValue (L.b.take n) (run (W.repairedTick w i) m s).basis) := sizes.2
      rw [yu,yv] at sy
      exact sy
    have record0 : (run Q [] u).basis=v.basis := run_basis_records Q u u [] (m.drop (measurementCount P)) rfl
    have orig := narrowSkywalkRecord_views L hv n (by omega) nlen
    have views := R.views n hw
    have xx : R.xp=L.half.take n := by rw [←views.1]; rw [orig.1]
    have yy : R.yp=L.b.take n := by rw [←views.2.1]; rw [orig.2.1]
    have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp gap hx cop hi s hs
    have uq : u.basis R.q=false := by
      apply (head_aux w i hi hn s _ L.history (List.mem_cons_self)).trans
      exact input.2.2.2.2.1
    have clean : regValue R.carryLow u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have qm : q∈L.carry := List.mem_of_mem_take hq
      apply (head_aux w i hi hn s _ q (List.mem_cons_of_mem _ qm)).trans
      exact (regValue_zero _ _).mp input.2.2.2.2.2 q qm
    have eq (r : List Bool) : run (narrowCopy R n) r u=run Q r u := by
      have a : Shape (n-2) (regValue R.xp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,xx,record0]
        exact shapeX
      have b : Band (n-2) (regValue R.yp u.basis) ↔
          Band (n-2) (regValue R.yp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,yy,record0]
        exact bandY
      simpa only [n2] using narrowCopy_eq (n-2) R hw' nd u r uq clean a b
    have counts : measurementCount (narrowCopy R n)=measurementCount Q := by
      simpa only [n2] using (narrowCopy_counts (n-2) R hw').2
    simp only [tick,if_pos band]
    rw [old_split _ _ band]
    change run ((P++narrowCopy R n)++E) m s=run ((P++Q)++E) m s
    conv_lhs => rw [List.append_assoc,run_append P (narrowCopy R n++E)]
    conv_rhs => rw [List.append_assoc,run_append P (Q++E)]
    change run (narrowCopy R n++E) (m.drop (measurementCount P)) u = run (Q++E) (m.drop (measurementCount P)) u
    rw [run_append (narrowCopy R n) E,run_append Q E]
    rw [run_take (narrowCopy R n),run_take Q,eq,counts]
  · simpa only [tick,if_neg band] using
      TickGap.tick_eq w hn x p i hp0 hx0 hpo hp (by norm_num [p]) hx cop hi s m hs

def due (i : Nat) : Nat := if 225 ≤ i ∧ i ≤ 254 then 1 else TickGap.due i

theorem tick_counts (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (tick w i)+due i=toffoliCount (W.repairedTick w i)  ∧
    measurementCount (tick w i)=measurementCount (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_counts (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,due,if_pos band,toffoliCount_append,measurementCount_append]
    exact ⟨by omega,by omega⟩
  · simpa only [tick,if_neg band,due,if_neg band] using TickGap.tick_counts w i hi hn

theorem tick_support (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    wires (tick w i) ⊆ wires (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_support (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)
  · simpa only [tick,if_neg band] using TickGap.tick_support w i hi hn

theorem tick_slots (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    Challenge.gateSlots (tick w i)  ≤  Challenge.gateSlots (W.repairedTick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_slots (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split _ _ band]
    simp only [tick,if_pos band,Challenge.gateSlots_append]
    omega
  · simpa only [tick,if_neg band] using TickGap.tick_slots w i hi hn

theorem tick_physical (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (tick w i) := by
  by_cases band : 225 ≤ i ∧ i ≤ 254
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowCopy_physical (n-2) R hw' (narrowSkywalkRecord_nodup L hv n (by omega) nlen)
    simp only [n2] at h
    dsimp only [R,n,L] at h
    have old := W.repairedTick_physical w i hi hn
    rw [old_split _ _ band] at old
    simp only [tick,if_pos band,gatePhysical_append] at old ⊢
    exact ⟨⟨old.1.1,h⟩,old.2⟩
  · simpa only [tick,if_neg band] using TickGap.tick_physical w i hi hn
end ECDSAAdd.Entrant.TickRanges
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickRanges
open Arithmetic MappedCompressed Secp256k1 History5 OB5

theorem tick_eq5 (x : Nat) (hx0 : 0 < x) (hx : x < p) (i : Nat) (hi : i < 512)
    (s : State) (m : List Bool) (hs : W.CompressedCompactStage5 base x p i s.basis) :
    run (tick base i) m s=run (W.repairedTick base i) m s := by
  obtain ⟨raw,hraw,hbits⟩ := hs
  have dis := Stack5.prefix_disjoint_layout base base_pool_nodup i i (Nat.le_refl i) hi
  have read : ∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset,s.basis q=raw.basis q := by
    intro q hq
    rw [hbits]
    exact run_preserves_outside _ _ _ q (fun he => Finset.disjoint_left.mp dis he hq)
  have old := W.repairedTick_support base i hi base_pool_nodup
  have fresh := (tick_support base i hi base_pool_nodup).trans old
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 < 2^256 := by norm_num [p]
  exact Stack5.local_replace _ _ _ fresh old s raw m m read
    (tick_eq base base_pool_nodup x i hx0 hx cop hi raw m hraw)

theorem block_eq (x : Nat) (hx0 : 0 < x) (hx : x < p) (i : Nat) (hi : i < 512)
    (s : State) (m : List Bool) (hs : W.CompressedCompactStage5 base x p i s.basis) :
    run (tick base i++FirstNonzeroCodec.pack8first base i) m s=run (W.repairedTick base i++FirstNonzeroCodec.pack8first base i) m s := by
  rw [run_append (tick base i),run_append (W.repairedTick base i),run_take (tick base i),run_take (W.repairedTick base i)]
  rw [tick_eq5 x hx0 hx i hi s m hs,(tick_counts base i hi base_pool_nodup).2]

def forward (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)++forward (i+1) n

/-- The replacement forward prefix has exactly the existing logical trajectory. -/
theorem forward_gen (x : Nat) (hx0 : 0 < x) (hx : x < p) (n : Nat) :
    ∀ i, 1 ≤ i → i+n ≤ 512 → ∀(s : State)(m : List Bool),
    W.CompressedCompactStage5 base x p i s.basis →
    run (forward i n) m (pullState (sig (i-1)) s)=
      pullState (sig (i+n-1)) (run (Stack5.forward5 base i n) m s) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hpGap : p+2^32 ≤ 2^256 := by norm_num [p]
  induction n with
  | zero => intro i _ _ s m _; simp only [forward,Stack5.forward5,run,Nat.add_zero]
  | succ n ih =>
    intro i h1 hb s m hs
    have hi : i ≤ 511 := by omega
    have z := StackOB5.stage_zero x i (by omega) s.basis hs
    rw [pull_step i hi s z.1 z.2]
    have cnt : measurementCount (renameProgram (sig i) (tick base i++FirstNonzeroCodec.pack8first base i))=
        measurementCount (W.repairedTick base i++FirstNonzeroCodec.pack8first base i) := by
      rw [(renameProgram_counts (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)).2]
      simp only [measurementCount_append,(tick_counts base i (by omega) base_pool_nodup).2]
    rw [forward,Stack5.forward5,run_append _ (forward (i+1) n),run_append _ (Stack5.forward5 base (i+1) n),cnt,StackOB5.forward_step_records,OB5.run_rename i hi]
    rw [block_eq x hx0 hx i (by omega) s _ hs]
    rw [StackOB5.forward_step_eq base base_pool_nodup x p i hp0 hx0 hpo hp hpGap hx cop _ _ hs]
    have next := (Stack5.step_spec base base_pool_nodup StackOB5.historyAbove x p i hp0 hx0 hpo hp hpGap hx
      cop (by omega) s (m.take (measurementCount (W.repairedTick base i++History5.packAfter base i))) hs).2
    have step := ih (i+1) (by omega) (by omega) _ (m.drop (measurementCount (W.repairedTick base i++History5.packAfter base i))) next
    rw [show i+1-1=i by omega] at step
    rw [step,show i+1+n-1=i+(n+1)-1 by omega]

theorem forward_eq (x : Nat) (hx0 : 0 < x) (hx : x < p) (i n : Nat) (h1 : 1 ≤ i) (hi : i+n ≤ 512)
    (s : State) (m : List Bool) (hs : W.CompressedCompactStage5 base x p i s.basis) :
    run (forward i n) m (pullState (sig (i-1)) s)=run (StackOB5.forward i n) m (pullState (sig (i-1)) s) := by
  rw [forward_gen x hx0 hx n i h1 hi s m hs,StackOB5.forward_gen x hx0 hx n i h1 hi s m hs]

def count (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => due i+count (i+1) n

theorem forward_metrics (i n : Nat) (hi : i+n ≤ 512) :
    toffoliCount (forward i n)+count i n=toffoliCount (StackOB5.forward i n)  ∧
    measurementCount (forward i n)=measurementCount (StackOB5.forward i n)  ∧
    Challenge.gateSlots (forward i n) ≤ Challenge.gateSlots (StackOB5.forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,StackOB5.forward,count]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have stepCounts := tick_counts base i (by omega) base_pool_nodup
    have slots := tick_slots base i (by omega) base_pool_nodup
    have a := renameProgram_counts (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)
    have b := renameProgram_counts (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)
    have c := Baselines.rename_gateSlots (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)
    have d := Baselines.rename_gateSlots (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)
    simp only [forward,StackOB5.forward,count,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at a b c d ⊢
    exact ⟨by omega,by omega,by omega⟩

theorem forward_support (i n : Nat) (hi : i+n ≤ 512) : wires (forward i n)⊆wires (StackOB5.forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,StackOB5.forward]
  | succ n ih =>
    have fresh := tick_support base i (by omega) base_pool_nodup
    have block : wires (tick base i++FirstNonzeroCodec.pack8first base i) ⊆ wires (W.repairedTick base i++FirstNonzeroCodec.pack8first base i) := by
      simp only [wires_append]
      exact Finset.union_subset_union fresh (Finset.Subset.refl _)
    have ren : wires (renameProgram (sig i) (tick base i++FirstNonzeroCodec.pack8first base i)) ⊆
        wires (renameProgram (sig i) (W.repairedTick base i++FirstNonzeroCodec.pack8first base i)) := by
      rw [renameProgram_support,renameProgram_support]
      exact Finset.image_mono (sig i) block
    simp only [forward,StackOB5.forward,wires_append]
    exact Finset.union_subset_union ren (ih (i+1) (by omega))

theorem forward_physical (i n : Nat) (hi : i+n ≤ 512) : GatePhysical (forward i n) := by
  induction n generalizing i with
  | zero => simp [forward,GatePhysical]
  | succ n ih =>
    have stepPhysical := tick_physical base i (by omega) base_pool_nodup
    have codec := (FirstNonzeroCodec.packet_physical base base_pool_nodup i (by omega)).1
    have ren := gatePhysical_rename (sig i) (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr ⟨stepPhysical,codec⟩)
    simp only [forward,gatePhysical_append]
    exact ⟨ren,ih (i+1) (by omega)⟩

theorem count_508 : count 1 508=62 := by decide +kernel
end ECDSAAdd.Entrant.TickRanges
end

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588TickGapWalk =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.TickGap1591Arithmetic
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Integer

/-! Forward TickGap on the checked A/B integer stage. The packet programs,
the three terminal ticks, and the complete reverse walk stay unchanged. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588TickGap
open Arithmetic MappedCompressed Secp256k1 OB5
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

theorem tick_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (i : Nat) (hi : i<512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base isA x p i s.basis) :
    run (TickRanges.tick base i) m s=run (W.repairedTick base i) m s := by
  obtain ⟨raw,oldStage,read⟩ := Rolling1588.Integer.old_stage_local
    base isA base_pool_nodup x p i hi s stage
  have old := W.repairedTick_support base i hi base_pool_nodup
  have fresh := (TickRanges.tick_support base i hi base_pool_nodup).trans old
  exact Stack5.local_replace _ _ _ fresh old s raw m m read
    (TickRanges.tick_eq5 x hx0 hx i hi raw m oldStage)

theorem block_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (i : Nat) (hi : i<512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base isA x p i s.basis) :
    run (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i) m s=
      run (W.repairedTick base i++Rolling1588.Integer.packFirst base isA i) m s := by
  rw [run_append (TickRanges.tick base i),run_append (W.repairedTick base i),
    run_take (TickRanges.tick base i),run_take (W.repairedTick base i),
    tick_run_eq isA x hx0 hx i hi s m stage,
    (TickRanges.tick_counts base i hi base_pool_nodup).2]

def forward (isA : Bool) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (sig i)
      (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)++
        forward isA (i+1) n

def count (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => TickRanges.due i+count (i+1) n

def stackForward (isA : Bool) : Program :=
  forward isA 1 508 ++
    renameProgram (sig 509) (tick509F++Rolling1588.packAtTick isA 509) ++
    renameProgram (sig 510) (tick510F++Rolling1588.packAtTick isA 510) ++
    renameProgram (sig 511) tickF

attribute [local irreducible] forward stackForward Rolling1588.forward
  Rolling1588.Integer.forward Rolling1588.stackForward

theorem forward_gen (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (n : Nat) :
    ∀i,1 ≤ i → i+n ≤ 512 → ∀(s : State)(m : List Bool),
      Rolling1588.Integer.Stage base isA x p i s.basis →
      run (forward isA i n) m (pullState (sig (i-1)) s)=
        pullState (sig (i+n-1)) (run (Rolling1588.Integer.regularForward base isA i n) m s) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  induction n with
  | zero =>
    intro i _ _ s m _
    simp only [forward,Rolling1588.Integer.regularForward,run,Nat.add_zero]
  | succ n ih =>
    intro i h1 bound s m stage
    have hi : i ≤ 511 := by omega
    have zero := Rolling1588.Integer.stage_zero isA x i (by omega) s.basis stage
    rw [pull_step i hi s zero.1 zero.2]
    have mapped := (renameProgram_counts (sig i)
      (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)).2
    have records :
        measurementCount (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)=
          measurementCount (W.repairedTick base i++Rolling1588.Integer.packAfter base isA i) := by
      rw [measurementCount_append,measurementCount_append,
        (TickRanges.tick_counts base i (by omega) base_pool_nodup).2,
        Rolling1588.Integer.packFirst_records]
    rw [forward,Rolling1588.Integer.regularForward,run_append,run_append,mapped,records,
      OB5.run_rename i hi,block_run_eq isA x hx0 hx i (by omega) s _ stage,
      Rolling1588.Integer.forward_step_eq base isA base_pool_nodup x p i
        hp0 hx0 hpo hp gap hx cop _ _ stage]
    have next := (Rolling1588.Integer.step_spec base isA base_pool_nodup
      StackOB5.historyAbove x p i hp0 hx0 hpo hp gap hx cop (by omega) s
        (m.take (measurementCount (W.repairedTick base i++
          Rolling1588.Integer.packAfter base isA i))) stage).2
    have rest := ih (i+1) (by omega) (by omega) _
      (m.drop (measurementCount (W.repairedTick base i++
        Rolling1588.Integer.packAfter base isA i))) next
    rw [show i+1-1=i by omega,show i+1+n-1=i+(n+1)-1 by omega] at rest
    exact rest

theorem forward_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (i n : Nat) (h1 : 1 ≤ i) (bound : i+n ≤ 512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base isA x p i s.basis) :
    run (forward isA i n) m (pullState (sig (i-1)) s)=
      run (Rolling1588.forward isA i n) m (pullState (sig (i-1)) s) := by
  rw [←Rolling1588.Integer.forward_eq_packets]
  rw [forward_gen isA x hx0 hx n i h1 bound s m stage,
    Rolling1588.Integer.forward_gen isA x hx0 hx n i h1 bound s m stage]

theorem forward_first_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (n : Nat) (bound : 1+n ≤ 512) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (forward isA 1 n) m s=run (Rolling1588.forward isA 1 n) m s := by
  have same := forward_run_eq isA x hx0 hx 1 n (Nat.le_refl 1) bound s m
    (Rolling1588.Integer.stage_one base isA x p s first)
  have start : pullState (sig (1-1)) s=s := by
    apply State.extensionality
    · rfl
    · funext q
      change s.basis (sig 0 q)=s.basis q
      rw [sig_zero]
  rwa [start] at same

private theorem forward_integer_metrics (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    toffoliCount (forward isA i n)+count i n=
        toffoliCount (Rolling1588.Integer.forward isA i n) ∧
      measurementCount (forward isA i n)=measurementCount (Rolling1588.Integer.forward isA i n) ∧
      Challenge.gateSlots (forward isA i n) ≤
        Challenge.gateSlots (Rolling1588.Integer.forward isA i n) := by
  induction n generalizing i with
  | zero =>
    simp [forward,Rolling1588.Integer.forward,count,toffoliCount,measurementCount,Challenge.gateSlots]
  | succ n ih =>
    have rest := ih (i+1) (by omega)
    have step := TickRanges.tick_counts base i (by omega) base_pool_nodup
    have slots := TickRanges.tick_slots base i (by omega) base_pool_nodup
    simp only [forward,Rolling1588.Integer.forward,count,toffoliCount_append,
      measurementCount_append,Challenge.gateSlots_append,
      (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
      Baselines.rename_gateSlots]
    exact ⟨by omega,by omega,by omega⟩

theorem forward_metrics (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    toffoliCount (forward isA i n)+count i n=toffoliCount (Rolling1588.forward isA i n) ∧
      measurementCount (forward isA i n)=measurementCount (Rolling1588.forward isA i n) ∧
      Challenge.gateSlots (forward isA i n) ≤ Challenge.gateSlots (Rolling1588.forward isA i n) := by
  simpa only [Rolling1588.Integer.forward_eq_packets] using
    forward_integer_metrics isA i n bound

theorem count_508 : count 1 508=62 := by decide +kernel

theorem stackForward_metrics (isA : Bool) :
    toffoliCount (stackForward isA)+62=toffoliCount (Rolling1588.stackForward isA) ∧
      measurementCount (stackForward isA)=measurementCount (Rolling1588.stackForward isA) ∧
      Challenge.gateSlots (stackForward isA) ≤ Challenge.gateSlots (Rolling1588.stackForward isA) := by
  have head := forward_metrics isA 1 508 (by omega)
  rw [count_508] at head
  simp only [stackForward,Rolling1588.stackForward,toffoliCount_append,
    measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

private theorem forward_integer_support (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    wires (forward isA i n)⊆wires (Rolling1588.Integer.forward isA i n) := by
  induction n generalizing i with
  | zero => simp [forward,Rolling1588.Integer.forward,wires]
  | succ n ih =>
    have block : wires (TickRanges.tick base i++Rolling1588.Integer.packFirst base isA i)⊆
        wires (W.repairedTick base i++Rolling1588.Integer.packFirst base isA i) := by
      rw [wires_append,wires_append]
      exact Finset.union_subset_union
        (TickRanges.tick_support base i (by omega) base_pool_nodup) (Finset.Subset.refl _)
    have placed := Finset.image_mono (sig i) block
    rw [←renameProgram_support,←renameProgram_support] at placed
    simp only [forward,Rolling1588.Integer.forward,wires_append]
    exact Finset.union_subset_union placed (ih (i+1) (by omega))

theorem forward_support (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    wires (forward isA i n)⊆wires (Rolling1588.forward isA i n) := by
  simpa only [Rolling1588.Integer.forward_eq_packets] using
    forward_integer_support isA i n bound

theorem stackForward_support (isA : Bool) :
    wires (stackForward isA)⊆wires (Rolling1588.stackForward isA) := by
  simp only [stackForward,Rolling1588.stackForward,wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.union_subset_union
      (forward_support isA 1 508 (by omega)) (Finset.Subset.refl _))
        (Finset.Subset.refl _)) (Finset.Subset.refl _)

private theorem append_run_eq (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem stackForward_run_eq (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackForward isA) m s=run (Rolling1588.stackForward isA) m s := by
  have same := append_run_eq (forward isA 1 508) (Rolling1588.forward isA 1 508)
    (renameProgram (sig 509) (tick509F++Rolling1588.packAtTick isA 509) ++
      renameProgram (sig 510) (tick510F++Rolling1588.packAtTick isA 510) ++
      renameProgram (sig 511) tickF) s m
    (forward_metrics isA 1 508 (by omega)).2.1
    (fun r=>forward_first_run_eq isA x hx0 hx 508 (by omega) s r first)
  simpa only [stackForward,Rolling1588.stackForward,List.append_assoc] using same

theorem stackForward_boundary (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackForward isA) m s=pullState (sig 511)
      (run (Rolling1588.allEncode base isA 102) []
        (run (W.compactSkywalkForward base 1 511) [] s)) := by
  rw [stackForward_run_eq isA x hx0 hx s m first]
  exact Rolling1588.stackForward_boundary isA hn hlo x hx0 hx s m first

theorem stack_roundtrip (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (mE mD : List Bool)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (Rolling1588.stackReverse isA) mD (run (stackForward isA) mE s)=s := by
  rw [stackForward_run_eq isA x hx0 hx s mE first]
  exact Rolling1588.stack_roundtrip isA hn hlo x hx0 hx s mE mD first

end ECDSAAdd.Entrant.Rolling1588TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588TickGapPhases =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588TickGapWalk
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Native
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Kernel
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588KernelResources

/-! The new forward phase has the exact old A/B State boundary. All native,
field, inverse, host, and caller interfaces are retained. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588TickGap
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Challenge Baselines
  FrontierEntry1591Callers OB5
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  forward stackForward Rolling1588.forward Rolling1588.stackForward Rolling1588.stackReverse
  FrontierEntry1591Native.forward FrontierEntry1591Native.inverse
  Rolling1588.firstPhase Rolling1588.lastPhase

def tailPhase (isA : Bool) : Program := stackForward isA++skywalkArithmeticClear base

def firstPhase (isA : Bool) : Program := FrontierEntry1591Native.forward base++tailPhase isA

def oldKernel (a b : Bool) (F : Program) : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a)++
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b))

def kernel (a b : Bool) (F : Program) : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (firstPhase a)++
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b))

def entryKernel : Program := kernel true false Rolling1588.entryFieldHosted
def exitKernel : Program := kernel false true Rolling1588.exitFieldHosted

attribute [local irreducible] tailPhase firstPhase oldKernel kernel entryKernel exitKernel
  Rolling1588.entryKernel Rolling1588.exitKernel

private theorem first_run_eq_of_stack (N F F0 C : Program) (s : State) (m : List Bool)
    (records : measurementCount F=measurementCount F0)
    (same : ∀mn mf,run F mf (run N mn s)=run F0 mf (run N mn s)) :
    run (N++(F++C)) m s=run (N++(F0++C)) m s := by
  simp only [run_append,records]
  rw [same]

theorem first_run_eq (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (firstPhase isA) m s=run (Rolling1588.firstPhase isA) m s := by
  have same (mn mf : List Bool) :
      run (stackForward isA) mf (run (FrontierEntry1591Native.forward base) mn s)=
        run (Rolling1588.stackForward isA) mf
          (run (FrontierEntry1591Native.forward base) mn s) :=
    stackForward_run_eq isA x hx0 hx _ mf
      (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  simpa only [firstPhase,tailPhase,Rolling1588.firstPhase,List.append_assoc] using
    first_run_eq_of_stack (FrontierEntry1591Native.forward base) (stackForward isA)
      (Rolling1588.stackForward isA) (skywalkArithmeticClear base) s m
      (stackForward_metrics isA).2.1 same

private theorem state_fact_of_eq (P : State→Prop) (a b : State)
    (same : a=b) (fact : P b) : P a := by
  cases same
  exact fact

theorem first_clean (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    ∀q∈FrontierEntry1591Native.workSites,(run (firstPhase isA) m s).basis q=false := by
  exact state_fact_of_eq
    (fun t=>∀q∈FrontierEntry1591Native.workSites,t.basis q=false)
    (run (firstPhase isA) m s) (run (Rolling1588Lifetime.firstPhase isA) m s)
    (first_run_eq isA hn x y hx0 hx s m input)
    (Rolling1588Lifetime.first_clean isA hn hlo x y hx0 hx s m input)

theorem first_phase (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    (run (firstPhase isA) m s).phase=s.phase := by
  exact state_fact_of_eq (fun t=>t.phase=s.phase)
    (run (firstPhase isA) m s) (run (Rolling1588Lifetime.firstPhase isA) m s)
    (first_run_eq isA hn x y hx0 hx s m input)
    (Rolling1588Lifetime.first_phase isA hn hlo x y hx0 hx s m input)

theorem first_boundary (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (firstPhase isA) m s=pullState (sig 511)
      (run (Rolling1588.allEncode base isA 102) []
        (run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) []
          (run (FrontierEntry1591Native.forward base)
            (m.take (measurementCount (FrontierEntry1591Native.forward base))) s)))) := by
  rw [first_run_eq isA hn x y hx0 hx s m input]
  exact Rolling1588Lifetime.first_boundary isA hn hlo x y hx0 hx s m input

theorem phases_roundtrip (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (mE mD : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (Rolling1588.lastPhase isA) mD (run (firstPhase isA) mE s)=s := by
  rw [first_run_eq isA hn x y hx0 hx s mE input]
  exact Rolling1588Lifetime.phases_roundtrip isA hn hlo x y hx0 hx s mE mD input

theorem first_metrics (isA : Bool) :
    toffoliCount (firstPhase isA)+62=toffoliCount (Rolling1588.firstPhase isA) ∧
      measurementCount (firstPhase isA)=measurementCount (Rolling1588.firstPhase isA) ∧
      gateSlots (firstPhase isA) ≤ gateSlots (Rolling1588.firstPhase isA) := by
  have stack := stackForward_metrics isA
  simp only [firstPhase,tailPhase,Rolling1588.firstPhase,toffoliCount_append,
    measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

theorem first_support (isA : Bool) :
    wires (firstPhase isA)⊆wires (Rolling1588.firstPhase isA) := by
  simp only [firstPhase,tailPhase,Rolling1588.firstPhase,wires_append,Finset.union_assoc]
  exact Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (stackForward_support isA) (Finset.Subset.refl _))

private theorem mapped_code_physical (isA : Bool) (f : Fin 10→Wire)
    (hf : Function.Injective f) :
    GatePhysical (renameProgram (MeasuredCodec5.label f) (Rolling1588.codeEncode isA)) := by
  have support : wires (Rolling1588.codeEncode isA)⊆Finset.range 10 := by
    simpa only [(Rolling1588.code_support isA).1] using
      (Finset.Subset.refl (Finset.range 10))
  exact gatePhysical_rename_support _ _
    (fun a ha b hb eq=>FirstNonzeroCodec.label_inj' f hf a (support ha) b (support hb) eq)
    (Rolling1588.code_physical isA).1

private theorem pack_physical (isA : Bool) (i : Nat) (hi : i<512) :
    GatePhysical (Rolling1588.packAtTick isA i) := by
  by_cases first : i=5
  · simp only [Rolling1588.packAtTick,if_pos first]
    exact (ParityCodec5New.first_mapped_physical _
      (History5.historyMap_injective base base_pool_nodup 0 (by decide))).1
  · simp only [Rolling1588.packAtTick,if_neg first]
    split
    · have due := History5.packDue_true i ‹History5.packDue i=true›
      exact mapped_code_physical isA _
        (History5.historyMap_injective base base_pool_nodup (i-5) (by omega))
    · simp [GatePhysical]

theorem forward_physical (isA : Bool) (i n : Nat) (bound : i+n ≤ 512) :
    GatePhysical (forward isA i n) := by
  induction n generalizing i with
  | zero => simp [forward,GatePhysical]
  | succ n ih =>
    have pack : GatePhysical (Rolling1588.Integer.packFirst base isA i) := by
      rw [Rolling1588.Integer.packFirst_base]
      exact pack_physical isA i (by omega)
    rw [forward,gatePhysical_append]
    exact ⟨gatePhysical_rename _ (sig_injective i (by omega)) _
      ((gatePhysical_append _ _).mpr
        ⟨TickRanges.tick_physical base i (by omega) base_pool_nodup,pack⟩),
      ih (i+1) (by omega)⟩

theorem stackForward_physical (isA : Bool) : GatePhysical (stackForward isA) := by
  have old := Rolling1588.stackForward_physical isA
  simp only [Rolling1588.stackForward,gatePhysical_append] at old
  simpa only [stackForward,gatePhysical_append] using
    And.intro (And.intro (And.intro (forward_physical isA 1 508 (by omega))
      old.1.1.2) old.1.2) old.2

theorem first_physical (isA : Bool) : GatePhysical (firstPhase isA) := by
  have old := Rolling1588.firstPhase_physical isA
  simp only [Rolling1588.firstPhase,gatePhysical_append] at old
  simpa only [firstPhase,tailPhase,gatePhysical_append] using
    And.intro old.1.1 (And.intro (stackForward_physical isA) old.2)

private theorem mapped_run_eq (f : Equiv.Perm Wire) (P Q : Program)
    (s : State) (m : List Bool) (clean : pullState f s=s)
    (same : run P m s=run Q m s) :
    run (renameProgram f P) m s=run (renameProgram f Q) m s := by
  apply pullState_perm_injective f
  rw [run_rename _ f.injective,run_rename _ f.injective,clean]
  exact same

theorem first_hosted_run_eq (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (renameProgram Rolling1588Lifetime.phaseHost (firstPhase isA)) m s=
      run (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase isA)) m s := by
  exact mapped_run_eq Rolling1588Lifetime.phaseHost _ _ s m
    (Rolling1588Lifetime.pull_phase_clean s
      (Rolling1588Lifetime.caller_phase_clean x y s input))
    (first_run_eq isA hn x y hx0 hx s m input)

private theorem append_run_eq_tickgap_phases (P Q R : Program) (s : State) (m : List Bool)
    (records : measurementCount P=measurementCount Q)
    (same : ∀r,run P r s=run Q r s) :
    run (P++R) m s=run (Q++R) m s := by
  rw [run_append,run_append,records,same]

theorem kernel_run_eq (a b : Bool) (F : Program)
    (hn : (skywalkSharedWires base).Nodup)
    (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (input : SkywalkArithmeticInput base x y s.basis) :
    run (kernel a b F) m s=run (oldKernel a b F) m s := by
  have records :
      measurementCount (renameProgram Rolling1588Lifetime.phaseHost (firstPhase a))=
        measurementCount (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(first_metrics a).2.1]
  simpa only [kernel,oldKernel] using append_run_eq_tickgap_phases
    (renameProgram Rolling1588Lifetime.phaseHost (firstPhase a))
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.firstPhase a))
    (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b)) s m records
    (fun r=>first_hosted_run_eq a hn x y hx0 hx s r input)

theorem kernel_metrics (a b : Bool) (F : Program) :
    toffoliCount (kernel a b F)+62=toffoliCount (oldKernel a b F) ∧
      measurementCount (kernel a b F)=measurementCount (oldKernel a b F) ∧
      gateSlots (kernel a b F) ≤ gateSlots (oldKernel a b F) := by
  have first := first_metrics a
  simp only [kernel,oldKernel,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

private theorem mapped_append_support (f : Wire→Wire) (P Q R : Program)
    (first : wires P⊆wires Q) :
    wires (renameProgram f P++R)⊆wires (renameProgram f Q++R) := by
  rw [wires_append,wires_append,renameProgram_support,renameProgram_support]
  exact Finset.union_subset_union
    (Finset.image_mono f first) (Finset.Subset.refl _)

theorem kernel_support (a b : Bool) (F : Program) :
    wires (kernel a b F)⊆wires (oldKernel a b F) := by
  simpa only [kernel,oldKernel] using
    mapped_append_support Rolling1588Lifetime.phaseHost
      (firstPhase a) (Rolling1588.firstPhase a)
      (F++renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase b)) (first_support a)

theorem kernel_physical (a b : Bool) (F : Program) (field : GatePhysical F) :
    GatePhysical (kernel a b F) := by
  simpa only [kernel,gatePhysical_append] using
    And.intro (Rolling1588Lifetime.phase_physical _ (first_physical a))
      (And.intro field
        (Rolling1588Lifetime.phase_physical _ (Rolling1588.lastPhase_physical b)))

theorem kernel_entry_correct (F : Program) (raw : EntryCorrect (oldKernel true false F)) :
    EntryCorrect (kernel true false F) := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have actual := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  rw [kernel_run_eq true false F hn x _ hx0 hx t m actual]
  exact raw hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half

theorem kernel_exit_correct (F : Program) (raw : ExitCorrect (oldKernel false true F)) :
    ExitCorrect (kernel false true F) := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  rw [kernel_run_eq false true F hn x Y.val hx0 hx s m input]
  exact raw hn hlo ho hf x Y hx0 hx s m input hg hs

theorem entry_correct : EntryCorrect entryKernel := by
  have old : EntryCorrect (oldKernel true false Rolling1588.entryFieldHosted) := by
    simpa only [oldKernel,Rolling1588.entryKernel] using Rolling1588.entry_correct
  simpa only [entryKernel] using kernel_entry_correct Rolling1588.entryFieldHosted old

theorem exit_correct : ExitCorrect exitKernel := by
  have old : ExitCorrect (oldKernel false true Rolling1588.exitFieldHosted) := by
    simpa only [oldKernel,Rolling1588.exitKernel] using Rolling1588.exit_correct
  simpa only [exitKernel] using kernel_exit_correct Rolling1588.exitFieldHosted old

private theorem metrics_of_shapes (P Q A B : Program)
    (left : P=A) (right : Q=B)
    (metrics : toffoliCount A+62=toffoliCount B ∧
      measurementCount A=measurementCount B ∧ gateSlots A ≤ gateSlots B) :
    toffoliCount P+62=toffoliCount Q ∧
      measurementCount P=measurementCount Q ∧ gateSlots P ≤ gateSlots Q := by
  cases left
  cases right
  exact metrics

theorem entryKernel_metrics :
    toffoliCount entryKernel+62=toffoliCount Rolling1588.entryKernel ∧
      measurementCount entryKernel=measurementCount Rolling1588.entryKernel ∧
      gateSlots entryKernel ≤ gateSlots Rolling1588.entryKernel := by
  have left : entryKernel=kernel true false Rolling1588.entryFieldHosted := by
    unfold entryKernel
    rfl
  have right : Rolling1588.entryKernel=oldKernel true false Rolling1588.entryFieldHosted := by
    unfold Rolling1588.entryKernel oldKernel
    rfl
  exact metrics_of_shapes entryKernel Rolling1588.entryKernel
    (kernel true false Rolling1588.entryFieldHosted)
    (oldKernel true false Rolling1588.entryFieldHosted) left right
    (kernel_metrics true false Rolling1588.entryFieldHosted)

theorem exitKernel_metrics :
    toffoliCount exitKernel+62=toffoliCount Rolling1588.exitKernel ∧
      measurementCount exitKernel=measurementCount Rolling1588.exitKernel ∧
      gateSlots exitKernel ≤ gateSlots Rolling1588.exitKernel := by
  have left : exitKernel=kernel false true Rolling1588.exitFieldHosted := by
    unfold exitKernel
    rfl
  have right : Rolling1588.exitKernel=oldKernel false true Rolling1588.exitFieldHosted := by
    unfold Rolling1588.exitKernel oldKernel
    rfl
  exact metrics_of_shapes exitKernel Rolling1588.exitKernel
    (kernel false true Rolling1588.exitFieldHosted)
    (oldKernel false true Rolling1588.exitFieldHosted) left right
    (kernel_metrics false true Rolling1588.exitFieldHosted)

theorem entryKernel_support_subset : wires entryKernel⊆wires Rolling1588.entryKernel := by
  simpa only [entryKernel,oldKernel,Rolling1588.entryKernel] using
    kernel_support true false Rolling1588.entryFieldHosted

theorem exitKernel_support_subset : wires exitKernel⊆wires Rolling1588.exitKernel := by
  simpa only [exitKernel,oldKernel,Rolling1588.exitKernel] using
    kernel_support false true Rolling1588.exitFieldHosted

theorem entryKernel_support : wires entryKernel⊆OB5Support.logicalSites :=
  entryKernel_support_subset.trans Rolling1588.entryKernel_support

theorem exitKernel_support : wires exitKernel⊆OB5Support.logicalSites :=
  exitKernel_support_subset.trans Rolling1588.exitKernel_support

theorem entryKernel_physical : GatePhysical entryKernel := by
  simpa only [entryKernel] using
    kernel_physical true false Rolling1588.entryFieldHosted Rolling1588.entryFieldHosted_physical

theorem exitKernel_physical : GatePhysical exitKernel := by
  simpa only [exitKernel] using
    kernel_physical false true Rolling1588.exitFieldHosted Rolling1588.exitFieldHosted_physical

theorem entryKernel_free (i : Nat) (hi : i∈logicalOmissions) : base i∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_free i hi (entryKernel_support_subset used)

theorem exitKernel_free (i : Nat) (hi : i∈logicalOmissions) : base i∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_free i hi (exitKernel_support_subset used)

theorem entryKernel_768_free : base 768∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_768_free (entryKernel_support_subset used)
theorem exitKernel_768_free : base 768∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_768_free (exitKernel_support_subset used)
theorem entryKernel_718_free : base 718∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_718_free (entryKernel_support_subset used)
theorem exitKernel_718_free : base 718∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_718_free (exitKernel_support_subset used)
theorem entryKernel_719_free : base 719∉wires entryKernel :=
  fun used=>Rolling1588.entryKernel_719_free (entryKernel_support_subset used)
theorem exitKernel_719_free : base 719∉wires exitKernel :=
  fun used=>Rolling1588.exitKernel_719_free (exitKernel_support_subset used)

end ECDSAAdd.Entrant.Rolling1588TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1TickGap =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Final
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588TickGapPhases

/-! E1 entries and the reflected square are unchanged. Only the two
forward tails use the checked TickGap program. Both inverse phases stay. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1TickGap
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def restE (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase true)++
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))

def restX (L : ControlledPointLayout) : Program :=
  renameProgram (wireFn2 L)
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false)++
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))

def entryStage (L : ControlledPointLayout) (kx ky : Fp) : Program :=
  fusedY L ky++E1QubitPlacement.entryM L kx++restE L

def secondStage (L : ControlledPointLayout) (k cy : Fp) : Program :=
  ReflectionE1.squareEntry L k++restX L++exitY L cy

theorem entry_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.entry Rolling1588TickGap.entryKernel L=
      E1QubitPlacement.tickF L++restE L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.entry,Rolling1588TickGap.entryKernel,
    Rolling1588TickGap.kernel,Rolling1588TickGap.firstPhase,restE,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

theorem exit_split (L : ControlledPointLayout) :
    FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L=
      E1QubitPlacement.tickF L++restX L := by
  have tick:=E1QubitPlacement.tick_eq L
  change renameProgram (wireFn2 L)
      (renameProgram Rolling1588Lifetime.phaseHost (FrontierEntry1591Native.forward base))=
        E1QubitPlacement.tickF L at tick
  simp only [FrontierEntry1591Callers.exit,Rolling1588TickGap.exitKernel,
    Rolling1588TickGap.kernel,Rolling1588TickGap.firstPhase,restX,
    renameProgram,List.map_append,List.append_assoc] at tick ⊢
  rw [tick]

section CorrectStages
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem entryStage_step (X Y kx ky : Fp) (G : Bool) (origin : BasisState)
    (hx : X+(if G then kx else 0)≠0) :
    Triple (PointDialogValues L X Y G origin) (entryStage L kx ky)
      (PointDialogValues L (X+(if G then kx else 0))
        ((Y+(if G then ky else 0))/(X+(if G then kx else 0))) G origin) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  have add:=fastStep_addX L hw hn X Y G origin kx
  have divide:=division_step Rolling1588TickGap.entryKernel Rolling1588TickGap.entryKernel_support
    Rolling1588TickGap.entry_correct L hw hn config.1 above config.2.1 config.2.2
    (X+(if G then kx else 0)) Y ky G origin hx
  have prior:=add.seq divide
  apply E1QubitPlacement.tri_transfer
    (A:=fusedY L ky++E1QubitPlacement.entryM L kx)
    (B:=fastConstAdd L L.point.x kx++fusedY L ky++E1QubitPlacement.tickF L)
    (R:=restE L)
  · intro s v m1 m2
    exact E1QubitPlacement.entry1_eq L hw hn kx ky s X.val X.isLt Y G
      v.x v.y v.generic v.clean m1 m2
  · simpa only [entryStage,division,entry_split,List.append_assoc] using prior

theorem secondStage_step (X Y k cy : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStage L k cy)
      (PointDialogValues L Z (Y*Z-(if G then cy else 0)) G origin) := by
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  have square:=SquareCarryLoan719BF.step L hw hn X Y G origin
  have add:=fastStep_addX L hw hn Z Y G origin k
  have multiply:=fusedMultiply_step L hw hn
    (FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L)
    (exit_correct Rolling1588TickGap.exitKernel Rolling1588TickGap.exitKernel_support
      Rolling1588TickGap.exit_correct L hw hn)
    (Z+(if G then k else 0)) Y cy G origin hx
  have prior:=(square.seq add).seq multiply
  simp only [secondStage,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=ReflectionE1.squareEntry L k)
    (B:=SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++E1QubitPlacement.tickF L)
    (R:=restX L++exitY L cy)
  · intro s v m1 m2
    exact ReflectionE1.squareEntry_eq L hw hn k X Y G origin s m1 m2 v
  · simpa only [secondStage,fusedMultiply,exit_split,List.append_assoc,Z] using prior

end CorrectStages

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  entryStage L (-cx) (-cy)++secondStage L (ReflectionE1.correction cx) cy++fastConstNeg L cx

def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clrF L++renameProgram (swapF L) (generic L cx cy)++clrF L

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  zrep L++mid L cx cy++zrep L

theorem gen_shape (L : ControlledPointLayout) (cx cy : Fp) :
    gen L cx cy=GenericQ5Geometry.wrapG L (generic L cx cy) := rfl

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=entryStage_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStage_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  have finish:=fastStep_negX L hw hn d (a*d-cy) true origin cx
  simp only [if_true] at finish
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at finish
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at second finish
  exact (first.seq second).seq finish

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=entryStage_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStage_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have finish:=fastStep_negX L hw hn X Y false origin cx
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second finish
  rw [back] at second
  exact (first.seq second).seq finish


theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (X.val ≠ 5) = fin) (h2 : decide (X'.val ≠ 5) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clrF_step L hw hn X Y G base
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
        L.point.finite ^^ decide (X'.val ≠ 5)) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := zrep_step L hw hn 0 5 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    have mid := midFFused_values L hw hn cx cy 5 0 5 0 false s.basis false
      (fun base' => generic_false L hw hn 5 0 cx cy base' finFive_ne_zero) hfin
      (by simp [finFive_val]) (by simp [finFive_val])
    have z2 := zrep_step L hw hn 5 0 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (x.val ≠ 5) = true := decide_eq_true (val_ne_five hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide ((genericX x y cx cy).val ≠ 5) = true :=
        decide_eq_true (val_ne_five (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end Correct
attribute [local irreducible] restE restX entryStage secondStage generic mid gen
  ReflectionE1.restE ReflectionE1.restX ReflectionE1.tailP ReflectionE1.generic ReflectionE1.gen
  Rolling1588TickGap.tailPhase Rolling1588TickGap.stackForward Rolling1588.stackForward
  Rolling1588.firstPhase Rolling1588.lastPhase Rolling1588.entryFieldHosted Rolling1588.exitFieldHosted

private theorem relation_of_shapes (R : Program→Program→Prop) (P Q A B : Program)
    (left : P=A) (right : Q=B) (fact : R A B) : R P Q := by
  cases left
  cases right
  exact fact

private theorem fact_of_shape (R : Program→Prop) (P Q : Program)
    (shape : P=Q) (fact : R Q) : R P := by
  cases shape
  exact fact

private def Facts (n : Nat) (P Q : Program) : Prop :=
  toffoliCount P+n=toffoliCount Q ∧ measurementCount P=measurementCount Q ∧
    gateSlots P ≤ gateSlots Q ∧ wires P⊆wires Q

private theorem append_facts (P Q C : Program)
    (count : toffoliCount P+62=toffoliCount Q ∧ measurementCount P=measurementCount Q ∧
      gateSlots P ≤ gateSlots Q) (sub : wires P⊆wires Q) : Facts 62 (P++C) (Q++C) := by
  simp only [Facts,toffoliCount_append,measurementCount_append,gateSlots_append,wires_append]
  exact ⟨by omega,by omega,by omega,Finset.union_subset_union sub (Finset.Subset.refl _)⟩

private theorem tail_facts (a : Bool) :
    Facts 62 (Rolling1588TickGap.tailPhase a) (ReflectionE1.tailP a) := by
  apply relation_of_shapes (Facts 62) _ _
    (Rolling1588TickGap.stackForward a++skywalkArithmeticClear base)
    (Rolling1588.stackForward a++skywalkArithmeticClear base)
  · unfold Rolling1588TickGap.tailPhase
    rfl
  · unfold ReflectionE1.tailP
    rfl
  · exact append_facts _ _ _ (Rolling1588TickGap.stackForward_metrics a)
      (Rolling1588TickGap.stackForward_support a)

private def restContext (f g : Wire→Wire) (P R : Program) : Program :=
  renameProgram f (renameProgram g P++R)

private theorem rest_facts (f g : Wire→Wire) (P Q R : Program) (h : Facts 62 P Q) :
    Facts 62 (restContext f g P R) (restContext f g Q R) := by
  rcases h with ⟨ht,hm,hs,hw⟩
  have sub : wires (restContext f g P R)⊆wires (restContext f g Q R) := by
    simp only [restContext,renameProgram_support,wires_append]
    exact Finset.image_mono f
      (Finset.union_subset_union (Finset.image_mono g hw) (Finset.Subset.refl _))
  simp only [Facts,restContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem restE_facts (L : ControlledPointLayout) :
    Facts 62 (restE L) (ReflectionE1.restE L) := by
  apply relation_of_shapes (Facts 62) _ _
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase true)
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (ReflectionE1.tailP true)
      (Rolling1588.entryFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase false)))
  · unfold restE restContext
    rfl
  · unfold ReflectionE1.restE restContext
    rfl
  · exact rest_facts _ _ _ _ _ (tail_facts true)

private theorem restX_facts (L : ControlledPointLayout) :
    Facts 62 (restX L) (ReflectionE1.restX L) := by
  apply relation_of_shapes (Facts 62) _ _
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false)
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))
    (restContext (wireFn2 L) Rolling1588Lifetime.phaseHost (ReflectionE1.tailP false)
      (Rolling1588.exitFieldHosted++
        renameProgram Rolling1588Lifetime.phaseHost (Rolling1588.lastPhase true)))
  · unfold restX restContext
    rfl
  · unfold ReflectionE1.restX restContext
    rfl
  · exact rest_facts _ _ _ _ _ (tail_facts false)

private def stagesContext (Y M E S X EY N : Program) : Program :=
  (Y++M++E)++(S++X++EY)++N

private theorem stages_facts (Y M E E0 S X X0 EY N : Program)
    (entry : Facts 62 E E0) (exit : Facts 62 X X0) :
    Facts 124 (stagesContext Y M E S X EY N) (stagesContext Y M E0 S X0 EY N) := by
  rcases entry with ⟨et,em,es,ew⟩
  rcases exit with ⟨xt,xm,xs,xw⟩
  have sub : wires (stagesContext Y M E S X EY N)⊆
      wires (stagesContext Y M E0 S X0 EY N) := by
    simp only [stagesContext,wires_append]
    exact Finset.union_subset_union
      (Finset.union_subset_union
        (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _)
          (Finset.Subset.refl _)) ew)
        (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) xw)
          (Finset.Subset.refl _))) (Finset.Subset.refl _)
  simp only [Facts,stagesContext,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy=stagesContext (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (exitY L cy) (fastConstNeg L cx) := by
  unfold generic entryStage secondStage stagesContext
  rfl

private theorem old_generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    ReflectionE1.generic L cx cy=stagesContext (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx) := by
  unfold ReflectionE1.generic ReflectionE1.entryStage ReflectionE1.secondStage stagesContext
  rfl

private theorem generic_facts (L : ControlledPointLayout) (cx cy : Fp) :
    Facts 124 (generic L cx cy) (ReflectionE1.generic L cx cy) := by
  exact relation_of_shapes (Facts 124) _ _ _ _
    (generic_shape L cx cy) (old_generic_shape L cx cy)
    (stages_facts (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx)
      (restE_facts L) (restX_facts L))

theorem generic_support_subset (L : ControlledPointLayout) (cx cy : Fp) :
    wires (generic L cx cy)⊆wires (ReflectionE1.generic L cx cy) :=
  (generic_facts L cx cy).2.2.2

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
  (generic_support_subset L cx cy).trans (ReflectionE1.generic_sites L hw hn cx cy)

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (generic L cx cy) :=
  fun used=>ReflectionE1.generic_free L hw hn cx cy i hi (generic_support_subset L cx cy used)

private theorem suffix_physical (P Q R : Program) (shape : P=Q++R)
    (physical : GatePhysical P) : GatePhysical R := by
  rw [shape,gatePhysical_append] at physical
  exact physical.2

private theorem restE_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restE L) := by
  have physical := placed_physical Rolling1588TickGap.entryKernel
    Rolling1588TickGap.entryKernel_support Rolling1588TickGap.entryKernel_physical L hw hn
  have entryPhysical : GatePhysical (FrontierEntry1591Callers.entry Rolling1588TickGap.entryKernel L) :=
    fact_of_shape GatePhysical _ _ (by unfold FrontierEntry1591Callers.entry;rfl) physical
  exact suffix_physical _ _ _ (entry_split L) entryPhysical

private theorem restX_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (restX L) := by
  have physical := placed_physical Rolling1588TickGap.exitKernel
    Rolling1588TickGap.exitKernel_support Rolling1588TickGap.exitKernel_physical L hw hn
  have exitPhysical : GatePhysical (FrontierEntry1591Callers.exit Rolling1588TickGap.exitKernel L) :=
    fact_of_shape GatePhysical _ _ (by unfold FrontierEntry1591Callers.exit;rfl) physical
  exact suffix_physical _ _ _ (exit_split L) exitPhysical

private theorem stages_physical (Y M E E0 S X X0 EY N : Program)
    (old : GatePhysical (stagesContext Y M E0 S X0 EY N))
    (entry : GatePhysical E) (exit : GatePhysical X) :
    GatePhysical (stagesContext Y M E S X EY N) := by
  simp only [stagesContext,gatePhysical_append] at old ⊢
  exact And.intro
    (And.intro (And.intro old.1.1.1 entry)
      (And.intro (And.intro old.1.2.1.1 exit) old.1.2.2)) old.2

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have old := fact_of_shape GatePhysical _ _ (old_generic_shape L cx cy).symm
    (ReflectionE1.generic_physical L hw hn cx cy)
  exact fact_of_shape GatePhysical _ _ (generic_shape L cx cy)
    (stages_physical (fusedY L (-cy)) (E1QubitPlacement.entryM L (-cx))
      (restE L) (ReflectionE1.restE L) (ReflectionE1.squareEntry L (ReflectionE1.correction cx))
      (restX L) (ReflectionE1.restX L) (exitY L cy) (fastConstNeg L cx) old
      (restE_physical L hw hn) (restX_physical L hw hn))

private def wrapContext (Z C : Program) (f : Wire→Wire) (P : Program) : Program :=
  Z++(C++renameProgram f P++C)++Z

private theorem wrap_facts (Z C : Program) (f : Wire→Wire) (P Q : Program)
    (h : Facts 124 P Q) : Facts 124 (wrapContext Z C f P) (wrapContext Z C f Q) := by
  rcases h with ⟨ht,hm,hs,hw⟩
  have sub : wires (wrapContext Z C f P)⊆wires (wrapContext Z C f Q) := by
    simp only [wrapContext,wires_append,renameProgram_support]
    exact Finset.union_subset_union
      (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.union_subset_union
          (Finset.union_subset_union (Finset.Subset.refl _) (Finset.image_mono f hw))
          (Finset.Subset.refl _))) (Finset.Subset.refl _)
  simp only [Facts,wrapContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem gen_facts (L : ControlledPointLayout) (cx cy : Fp) :
    Facts 124 (gen L cx cy) (ReflectionE1.gen L cx cy) := by
  apply relation_of_shapes (Facts 124) _ _
    (wrapContext (zrep L) (clrF L) (swapF L) (generic L cx cy))
    (wrapContext (zrep L) (clrF L) (swapF L) (ReflectionE1.generic L cx cy))
  · unfold gen mid wrapContext
    rfl
  · unfold ReflectionE1.gen ReflectionE1.mid wrapContext
    rfl
  · exact wrap_facts _ _ _ _ _ (generic_facts L cx cy)

theorem gen_metrics (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+124=toffoliCount (ReflectionE1.gen L cx cy) ∧
    measurementCount (gen L cx cy)=measurementCount (ReflectionE1.gen L cx cy) ∧
    gateSlots (gen L cx cy) ≤ gateSlots (ReflectionE1.gen L cx cy) :=
  ⟨(gen_facts L cx cy).1,(gen_facts L cx cy).2.1,(gen_facts L cx cy).2.2.1⟩

theorem gen_support_subset (L : ControlledPointLayout) (cx cy : Fp) :
    wires (gen L cx cy)⊆wires (ReflectionE1.gen L cx cy) := (gen_facts L cx cy).2.2.2

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  (gen_support_subset L cx cy).trans (ReflectionE1.gen_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z:=zrep_physical L hn
  have c:=clrF_physical L hw hn
  have g:=gatePhysical_rename (swapF L) (swapF_injective L hw hn) _ (generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append] using And.intro (And.intro z (And.intro (And.intro c g) c)) z

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 1588 := by
  rw [gen_shape]
  apply Rolling1588BFInventory.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy) _
    (generic_free layout layout_widths layout_nodup cx cy 768 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 718 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 719 (by simp)) C cy
  intro i hi
  apply generic_free layout layout_widths layout_nodup cx cy i
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

private theorem wrapper_facts (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Facts 124 P Q) :
    toffoliCount (Edges.wrapper L C cy P)+124=toffoliCount (Edges.wrapper L C cy Q) ∧
    measurementCount (Edges.wrapper L C cy P)=measurementCount (Edges.wrapper L C cy Q) ∧
    gateSlots (Edges.wrapper L C cy P) ≤ gateSlots (Edges.wrapper L C cy Q) := by
  rcases h with ⟨ht,hm,hs,_⟩
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 2152469 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout cx cy)).1
  have old:=ReflectionE1.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 1499210 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout cx cy)).2.1
  have old:=ReflectionE1.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 50166097 := by
  have diff:=(wrapper_facts layout C cy _ _ (gen_facts layout cx cy)).2.2
  have old:=ReflectionE1.wrapper_slots C cx cy
  omega

end ECDSAAdd.Entrant.ReflectionE1TickGap
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1TickGapFinal =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1TickGap

/-! E1/reflected Q1588 point with the two checked TickGap forward tails. -/
namespace ECDSAAdd.Entrant.ReflectionE1TickGap
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2152469,1499210,1588,50166097⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2152469 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1499210 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C) ≤ 1588 := by
  cases C with
  | zero => change qubits [] ≤ 1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50166097 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1499210
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50166097
    rw [normalize_slots];exact program_gateSlots C


end ECDSAAdd.Entrant.ReflectionE1TickGap
end -- original module boundary

-- Checked Low48 dependencies follow; the selected reflected prefix retains both checked TickGap tails.

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Square =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareResources
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Square

/-! Only the retained E1 square prefix changes. The reflected entry and all maps stay fixed. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1Low48Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

abbrev K : Nat := ControlLoan1589BFFold.K

def core (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.branchCK L ext control++LowZero18Square.branchBF L ext control++
    LowZero18Square.branchAF L ext control

def fastCore (L : ControlledPointLayout) : Program :=
  core L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def program (L : ControlledPointLayout) : Program :=
  SquareCarryLoan719BF.place L (fastCore L)

theorem raw_split (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) :
    LowZero18Square.raw L ext control=core L ext control++LowZero18Square.reflection L ext := rfl

theorem program_split (L : ControlledPointLayout) :
    LowZero18Square.program L=program L++ReflectionE1Square.reflectedTail L := by
  change SquareCarryLoan719BF.place L (LowZero18Square.raw L.dialogStreamedSquareWide
      (OwnDiagAll12Square.kext L) L.core.generic)=
    SquareCarryLoan719BF.place L (core L.dialogStreamedSquareWide
      (OwnDiagAll12Square.kext L) L.core.generic)++
    SquareCarryLoan719BF.place L (SquareCarryLoan719BF.reflection
      L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L))
  rw [raw_split,ReflectionE1Square.place_append]
  rfl

theorem raw_core_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (core L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (core L ext control) records s).basis=
      SquareReduction.p-1-
        (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
          (if s.basis control then K else 0))%SquareReduction.p) ∧
    ∀q,q∉L.core.out → (run (core L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := ControlLoan1589BFFold.resAF PA OB enabled
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have low (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.low t=A := regValue_congr _ _ _ (fun q hq => hf.2 q (lowAway q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.high t=B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.sum t=B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.product t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue ext t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (LowZero18Square.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := LowZero18Square.branchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (LowZero18Square.branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := LowZero18Square.branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (LowZero18Square.branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := LowZero18Square.branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OB hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := (stepC.seq stepB).seq stepA
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := ControlLoan1589BFFold.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  have oaLt : OA<SquareReduction.p := ofCast_lt _ _
  have reflected : OA=SquareReduction.p-1-
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) := by
    change SquareReduction.p-1-OA=
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) at exactResult
    omega
  exact ⟨phase,value.trans reflected,frame⟩


open Secp256k1 MappedCompressed CompressedPointDialog

theorem fastCore_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(((X+p-(if B then Y*Y else 0)%p)%p+(if B then ControlLoan1589BFFold.K else 0))%p) ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (OwnDiagAll12Square.kext_mem L hw q hq))
  have extOK:=OwnDiagAll12Square.kext_ok L hw hn
  have hext : ECDSAAdd.Entrant.ExtOK K L.core.generic (OwnDiagAll12Square.kext L) :=
    ⟨extOK.nodup,extOK.away,extOK.len⟩
  have kernel := raw_core_correct K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean hext hz
  simpa only [fastCore,hb,hp,pow_two] using kernel


private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

private theorem sub_val (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

theorem fastCore_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  have fresh:=fastCore_correct L hw hn X.val Y.val G X.isLt s m v.generic v.x v.y v.clean
  refine ⟨fresh.1,?_,fresh.2.2⟩
  have hK : ((SquareCarryLoan719BF.K:Nat):Fp).val=SquareCarryLoan719BF.K :=
    ZMod.val_natCast_of_lt (by norm_num [SquareCarryLoan719BF.K,ControlLoan1589BFFold.K,p])
  rw [ZMod.val_add,sub_val]
  cases G
  · simpa using fresh.2.1
  · simpa [ZMod.val_mul,hK,K,SquareCarryLoan719BF.K] using fresh.2.1

private theorem pool_away_x (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have dis:=(List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  intro hx
  have resident : q∈CompressedPointSquare.residents L := by
    simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis resident hq

theorem boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (program L) m s).phase=s.phase ∧
    regValue L.point.x (run (program L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (program L) m s).basis q=s.basis q := by
  have result:=fastCore_boundary L hw hn X Y G origin s m v
  obtain ⟨out,heq⟩ : ∃out : State,run (fastCore L) m s=out := ⟨_,rfl⟩
  rw [heq] at result
  have clean : regValue L.dialogPool out.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x L hn q hq)),v.clean]
  have eq:=ReflectionE1Square.place_run_eq L hw (fastCore L) s m v.clean (by rw [heq];exact clean)
  change run (program L) m s=run (fastCore L) m s at eq
  rw [eq,heq]
  exact result

theorem cleanup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    regValue L.dialogPool (run (program L) m s).basis=0 := by
  have result:=boundary L hw hn X Y G origin s m v
  obtain ⟨out,heq⟩ : ∃out : State,run (program L) m s=out := ⟨_,rfl⟩
  rw [heq] at result ⊢
  exact (regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x L hn q hq))).trans v.clean

/-- This comparison is separate from the direct boundary proof. -/
theorem run_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (mNew mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) mNew s=run (ReflectionE1Square.program L) mOld s := by
  obtain ⟨a,ha⟩ : ∃a : State,run (program L) mNew s=a := ⟨_,rfl⟩
  obtain ⟨b,hb⟩ : ∃b : State,run (ReflectionE1Square.program L) mOld s=b := ⟨_,rfl⟩
  have fresh:=boundary L hw hn X Y G origin s mNew v
  have prior:=ReflectionE1Square.boundary L hw hn X Y G origin s mOld v
  rw [ha] at fresh
  rw [hb] at prior
  rw [ha,hb]
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · funext q
    by_cases hx : q∈L.point.x
    · exact (regValue_eq_iff _ _ _).mp (fresh.2.1.trans prior.2.1.symm) q hx
    · exact (fresh.2.2 q hx).trans (prior.2.2 q hx).symm

private theorem window_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (LowZero18Square.withLowK2 L ext control src dst body)+48=
      toffoliCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) ∧
    measurementCount (LowZero18Square.withLowK2 L ext control src dst body)+18=
      measurementCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have a:=LowZero18Square.withLowK2_counts_diff L hw ext control src dst body h128 h129 hd he
  have b:=LowZero18Square.withLowK2_counts_diff L hw ext control src dst body h128 h129 hd he
  constructor <;> omega

private theorem window_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (LowZero18Square.withLowK2 L ext control src dst body)⊆
      wires (SquareCarryLoan719BF.withLowK2 L ext control src dst body) :=
  LowZero18Square.withLowK2_support_subset L hw ext control src dst body h128 h129 hd he

private theorem window_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst body)≤
      Challenge.gateSlots (SquareCarryLoan719BF.withLowK2 L ext control src dst body) :=
  LowZero18Square.withLowK2_slots_le L hw ext control src dst body h128 h129 hd he

private theorem core_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    toffoliCount (core L ext control)+144=toffoliCount (ReflectionE1Square.core L ext control) ∧
    measurementCount (core L ext control)+54=measurementCount (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_counts L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  have b:=window_counts L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_counts L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,toffoliCount_append,measurementCount_append]
  constructor <;> omega

private theorem core_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    wires (core L ext control)⊆wires (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_support L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  have b:=window_support L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_support L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact c | exact b | exact a | exact Finset.Subset.refl _

private theorem core_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (core L ext control)≤Challenge.gateSlots (ReflectionE1Square.core L ext control) := by
  have low:=L.core.low_length hw.core
  have high:=L.core.high_length hw.core
  have sum:=L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c:=window_slots L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  have b:=window_slots L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a:=window_slots L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  simp only [core,ReflectionE1Square.core,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,Challenge.gateSlots_append]
  omega

theorem counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+144=toffoliCount (ReflectionE1Square.program L) ∧
    measurementCount (program L)+54=measurementCount (ReflectionE1Square.program L) := by
  have h:=core_counts_diff L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,ReflectionE1Square.program,fastCore,ReflectionE1Square.fastCore,
    (ReflectionE1Square.place_counts _ _).1,(ReflectionE1Square.place_counts _ _).2] using h

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=51984 ∧ measurementCount (program L)=52766 := by
  have a:=counts_diff L hw
  have b:=ReflectionE1Square.counts L hw
  constructor <;> omega

theorem support_subset (L : ControlledPointLayout) (hw : L.Widths) :
    wires (program L)⊆wires (ReflectionE1Square.program L) := by
  unfold program ReflectionE1Square.program SquareCarryLoan719BF.place
  repeat' apply OneFlagReplay.rename_subset
  exact core_support_subset L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L hw).trans (ReflectionE1Square.support L hw hn)

theorem free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program L) :=
  fun used=>ReflectionE1Square.free L hw hn i hi (support_subset L hw used)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  have full:=LowZero18Square.physical L hw hn
  rw [program_split,gatePhysical_append] at full
  exact full.1

theorem slots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (ReflectionE1Square.program L) := by
  have h:=core_slots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,ReflectionE1Square.program,fastCore,ReflectionE1Square.fastCore,
    SquareCarryLoan719BF.place,Baselines.rename_gateSlots] using h

end ECDSAAdd.Entrant.ReflectionE1Low48Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Generic =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1TickGapFinal
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Low48Square

/-! Keep the checked E1 entries and TickGap tails. Replace only the reflected square prefix. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1TickGapLow48
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def squareEntry (L : ControlledPointLayout) (k : Fp) : Program :=
  ReflectionE1Low48Square.program L++E1ReflectedPlacement.entryR L k

def secondStage (L : ControlledPointLayout) (k cy : Fp) : Program :=
  squareEntry L k++ReflectionE1TickGap.restX L++exitY L cy


theorem squareEntry_base (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m1 m2 : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (squareEntry L k) m1 s=
      run (SquareCarryLoan719BF.program L++fastConstAdd L L.point.x k++
        E1QubitPlacement.tickF L) m2 s := by
  let n1:=measurementCount (ReflectionE1Low48Square.program L)
  let n2:=measurementCount (SquareCarryLoan719BF.program L)
  obtain ⟨a,ha⟩ : ∃a : State,run (ReflectionE1Low48Square.program L) (m1.take n1) s=a := ⟨_,rfl⟩
  obtain ⟨r,hr⟩ : ∃r : State,run (SquareCarryLoan719BF.program L) (m2.take n2) s=r := ⟨_,rfl⟩
  have fresh:=ReflectionE1Low48Square.boundary L hw hn X Y G origin s (m1.take n1) v
  have prior:=SquareCarryLoan719BF.step L hw hn X Y G origin s (m2.take n2) v
  rw [ha] at fresh
  rw [hr] at prior
  let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  let R:=p-1-Z.val
  have ppos : 0<p := by norm_num [p]
  have rp : R<p := by
    change p-1-Z.val<p
    omega
  have ax : regValue L.point.x a.basis=R:=fresh.2.1
  have ag : a.basis L.core.generic=G :=
    (fresh.2.2 _ (((E1QubitPlacement.lay L hw hn _).2.2 rfl).1)).trans v.generic
  have ac : regValue L.dialogPool a.basis=0 := by
    rw [regValue_congr _ _ s.basis
      (fun q hq=>fresh.2.2 q (((E1QubitPlacement.lay L hw hn q).2.1 hq).1)),v.clean]
  have involution (n : Nat) (bound : n<p) : n=p-1-(p-1-n) := by omega
  have rx : regValue L.point.x r.basis=p-1-R := by
    have value : regValue L.point.x r.basis=Z.val:=prior.2.x
    exact value.trans (involution Z.val Z.isLt)
  have outside (q : Wire) (hq : q∉L.point.x) : r.basis q=a.basis q := by
    have oldFrame : r.basis q=s.basis q := by
      by_cases hy : q∈L.point.y
      · exact (regValue_eq_iff _ _ _).mp (prior.2.y.trans v.y.symm) q hy
      · have away : q∉L.point.x++L.point.y:=by simp only [List.mem_append,not_or];exact ⟨hq,hy⟩
        exact (prior.2.rest q away).trans (v.rest q away).symm
    exact oldFrame.trans (fresh.2.2 q hq).symm
  have eq:=E1ReflectedPlacement.entryR_eq L hw hn k a r R rp G ax ag ac
    (prior.1.trans fresh.1.symm) rx outside (m1.drop n1) (m2.drop n2)
  simpa only [squareEntry,run_append,n1,n2,ha,hr,List.append_assoc] using eq

theorem squareEntry_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (mNew mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (squareEntry L k) mNew s=run (ReflectionE1.squareEntry L k) mOld s :=
  (squareEntry_base L hw hn k X Y G origin s mNew [] v).trans
    (ReflectionE1.squareEntry_eq L hw hn k X Y G origin s mOld [] v).symm

section CorrectStages
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem secondStage_step (X Y k cy : Fp) (G : Bool) (origin : BasisState)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)≠0) :
    let Z:=X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+
      (if G then k else 0)
    Triple (PointDialogValues L X Y G origin) (secondStage L k cy)
      (PointDialogValues L Z (Y*Z-(if G then cy else 0)) G origin) := by
  have prior:=ReflectionE1TickGap.secondStage_step L hw hn X Y k cy G origin hx
  simp only [secondStage,List.append_assoc]
  apply E1QubitPlacement.tri_transfer
    (A:=squareEntry L k) (B:=ReflectionE1.squareEntry L k)
    (R:=ReflectionE1TickGap.restX L++exitY L cy)
  · intro s v m1 m2
    exact squareEntry_eq L hw hn k X Y G origin s m1 m2 v
  · simpa only [ReflectionE1TickGap.secondStage,List.append_assoc] using prior

end CorrectStages

def generic (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  ReflectionE1TickGap.entryStage L (-cx) (-cy)++secondStage L (ReflectionE1.correction cx) cy++fastConstNeg L cx

def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clrF L++renameProgram (swapF L) (generic L cx cy)++clrF L

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  zrep L++mid L cx cy++zrep L

theorem gen_shape (L : ControlledPointLayout) (cx cy : Fp) :
    gen L cx cy=GenericQ5Geometry.wrapG L (generic L cx cy) := rfl

section Correct
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem generic_true (X Y cx cy : Fp) (origin : BasisState) (hX : X≠cx)
    (hd : cx-genericX X Y cx cy≠0) :
    Triple (PointDialogValues L X Y true origin) (generic L cx cy)
      (PointDialogValues L (genericX X Y cx cy) (genericY X Y cx cy) true origin) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hv:=generic_inplace_values X Y cx cy hX
  have first:=ReflectionE1TickGap.entryStage_step L hw hn X Y (-cx) (-cy) true origin
    (by simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hX)
  have ha : (Y-cy)/(X-cx)=a:=rfl
  simp only [if_true,←sub_eq_add_neg,ha] at first
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  have second:=secondStage_step L hw hn (X-cx) a (ReflectionE1.correction cx) cy true origin
    (by simpa only [if_true,hd4] using hd)
  simp only [if_true,hd4] at second
  have finish:=fastStep_negX L hw hn d (a*d-cy) true origin cx
  simp only [if_true] at finish
  rw [show cx-d=genericX X Y cx cy by dsimp [d];ring] at finish
  rw [show a*d-cy=genericY X Y cx cy from hv.2.2] at second finish
  exact (first.seq second).seq finish

theorem generic_false (X Y cx cy : Fp) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y false origin) (generic L cx cy)
      (PointDialogValues L X Y false origin) := by
  have first:=ReflectionE1TickGap.entryStage_step L hw hn X Y (-cx) (-cy) false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero] using hX)
  have second:=secondStage_step L hw hn X (Y/X) (ReflectionE1.correction cx) cy false origin
    (by simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX)
  have finish:=fastStep_negX L hw hn X Y false origin cx
  have back : Y/X*X=Y:=div_mul_cancel₀ Y hX
  simp only [Bool.false_eq_true,if_false,add_zero,sub_zero] at first second finish
  rw [back] at second
  exact (first.seq second).seq finish


theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (X.val ≠ 5) = fin) (h2 : decide (X'.val ≠ 5) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clrF_step L hw hn X Y G base
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (X.val ≠ 5)))
        L.point.finite ^^ decide (X'.val ≠ 5)) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := zrep_step L hw hn 0 5 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    have mid := midFFused_values L hw hn cx cy 5 0 5 0 false s.basis false
      (fun base' => generic_false L hw hn 5 0 cx cy base' finFive_ne_zero) hfin
      (by simp [finFive_val]) (by simp [finFive_val])
    have z2 := zrep_step L hw hn 5 0 0 false s.basis (by rw [hfin, finFive_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (x.val ≠ 5) = true := decide_eq_true (val_ne_five hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide ((genericX x y cx cy).val ≠ 5) = true :=
        decide_eq_true (val_ne_five (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end Correct

attribute [local irreducible] squareEntry secondStage generic mid gen
  ReflectionE1.squareEntry ReflectionE1Square.program ReflectionE1Low48Square.program
  ReflectionE1TickGap.entryStage ReflectionE1TickGap.secondStage ReflectionE1TickGap.restX
  ReflectionE1TickGap.generic ReflectionE1TickGap.gen

private theorem relation_of_shapes (R : Program→Program→Prop) (P Q A B : Program)
    (left : P=A) (right : Q=B) (fact : R A B) : R P Q := by
  cases left
  cases right
  exact fact

private theorem fact_of_shape (R : Program→Prop) (P Q : Program)
    (shape : P=Q) (fact : R Q) : R P := by
  cases shape
  exact fact

private def Facts (P Q : Program) : Prop :=
  toffoliCount P+144=toffoliCount Q ∧ measurementCount P+54=measurementCount Q ∧
    gateSlots P≤gateSlots Q ∧ wires P⊆wires Q

private def context (A P B : Program) : Program := A++(P++B)

private theorem context_facts (A P Q B : Program) (h : Facts P Q) :
    Facts (context A P B) (context A Q B) := by
  rcases h with ⟨ht,hm,hs,hw⟩
  have sub : wires (context A P B)⊆wires (context A Q B) := by
    simp only [context,wires_append]
    exact Finset.union_subset_union (Finset.Subset.refl _)
      (Finset.union_subset_union hw (Finset.Subset.refl _))
  simp only [Facts,context,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega,sub⟩

private def suffix (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  E1ReflectedPlacement.entryR L (ReflectionE1.correction cx)++ReflectionE1TickGap.restX L++
    exitY L cy++fastConstNeg L cx

private theorem generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    generic L cx cy=context (ReflectionE1TickGap.entryStage L (-cx) (-cy))
      (ReflectionE1Low48Square.program L) (suffix L cx cy) := by
  unfold generic secondStage squareEntry context suffix
  simp only [List.append_assoc]

private theorem old_generic_shape (L : ControlledPointLayout) (cx cy : Fp) :
    ReflectionE1TickGap.generic L cx cy=context (ReflectionE1TickGap.entryStage L (-cx) (-cy))
      (ReflectionE1Square.program L) (suffix L cx cy) := by
  unfold ReflectionE1TickGap.generic ReflectionE1TickGap.secondStage ReflectionE1.squareEntry context suffix
  simp only [List.append_assoc]

private theorem generic_facts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Facts (generic L cx cy) (ReflectionE1TickGap.generic L cx cy) := by
  have square : Facts (ReflectionE1Low48Square.program L) (ReflectionE1Square.program L) :=
    ⟨(ReflectionE1Low48Square.counts_diff L hw).1,(ReflectionE1Low48Square.counts_diff L hw).2,
      ReflectionE1Low48Square.slots_le L hw,ReflectionE1Low48Square.support_subset L hw⟩
  exact relation_of_shapes Facts _ _ _ _ (generic_shape L cx cy) (old_generic_shape L cx cy)
    (context_facts (ReflectionE1TickGap.entryStage L (-cx) (-cy)) _ _ (suffix L cx cy) square)

theorem generic_support_subset (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (generic L cx cy)⊆wires (ReflectionE1TickGap.generic L cx cy) :=
  (generic_facts L hw cx cy).2.2.2

theorem generic_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (generic L cx cy)⊆(OB5Support.sites L).toFinset :=
  (generic_support_subset L hw cx cy).trans (ReflectionE1TickGap.generic_sites L hw hn cx cy)

theorem generic_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (generic L cx cy) :=
  fun used=>ReflectionE1TickGap.generic_free L hw hn cx cy i hi
    (generic_support_subset L hw cx cy used)

private theorem context_physical (A P Q B : Program) (old : GatePhysical (context A Q B))
    (fresh : GatePhysical P) : GatePhysical (context A P B) := by
  simp only [context,gatePhysical_append] at old ⊢
  exact ⟨old.1,fresh,old.2.2⟩

theorem generic_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (generic L cx cy) := by
  have old:=fact_of_shape GatePhysical _ _ (old_generic_shape L cx cy).symm
    (ReflectionE1TickGap.generic_physical L hw hn cx cy)
  exact fact_of_shape GatePhysical _ _ (generic_shape L cx cy)
    (context_physical (ReflectionE1TickGap.entryStage L (-cx) (-cy))
      (ReflectionE1Low48Square.program L) (ReflectionE1Square.program L) (suffix L cx cy) old
      (ReflectionE1Low48Square.physical L hw hn))

private def wrapContext (Z C : Program) (f : Wire→Wire) (P : Program) : Program :=
  Z++(C++renameProgram f P++C)++Z

private theorem wrap_facts (Z C : Program) (f : Wire→Wire) (P Q : Program) (h : Facts P Q) :
    Facts (wrapContext Z C f P) (wrapContext Z C f Q) := by
  rcases h with ⟨ht,hm,hs,hw⟩
  have sub : wires (wrapContext Z C f P)⊆wires (wrapContext Z C f Q) := by
    simp only [wrapContext,wires_append,renameProgram_support]
    exact Finset.union_subset_union
      (Finset.union_subset_union (Finset.Subset.refl _)
        (Finset.union_subset_union
          (Finset.union_subset_union (Finset.Subset.refl _) (Finset.image_mono f hw))
          (Finset.Subset.refl _))) (Finset.Subset.refl _)
  simp only [Facts,wrapContext,toffoliCount_append,measurementCount_append,gateSlots_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega,sub⟩

private theorem gen_facts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Facts (gen L cx cy) (ReflectionE1TickGap.gen L cx cy) := by
  apply relation_of_shapes Facts _ _
    (wrapContext (zrep L) (clrF L) (swapF L) (generic L cx cy))
    (wrapContext (zrep L) (clrF L) (swapF L) (ReflectionE1TickGap.generic L cx cy))
  · unfold gen mid wrapContext
    rfl
  · unfold ReflectionE1TickGap.gen ReflectionE1TickGap.mid wrapContext
    rfl
  · exact wrap_facts _ _ _ _ _ (generic_facts L hw cx cy)

theorem gen_metrics (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+144=toffoliCount (ReflectionE1TickGap.gen L cx cy) ∧
    measurementCount (gen L cx cy)+54=measurementCount (ReflectionE1TickGap.gen L cx cy) ∧
    gateSlots (gen L cx cy)≤gateSlots (ReflectionE1TickGap.gen L cx cy) :=
  ⟨(gen_facts L hw cx cy).1,(gen_facts L hw cx cy).2.1,(gen_facts L hw cx cy).2.2.1⟩

theorem gen_support_subset (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (gen L cx cy)⊆wires (ReflectionE1TickGap.gen L cx cy) :=
  (gen_facts L hw cx cy).2.2.2

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  (gen_support_subset L hw cx cy).trans (ReflectionE1TickGap.gen_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z:=zrep_physical L hn
  have c:=clrF_physical L hw hn
  have g:=gatePhysical_rename (swapF L) (swapF_injective L hw hn) _ (generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append] using And.intro (And.intro z (And.intro (And.intro c g) c)) z

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1588 := by
  rw [gen_shape]
  apply Rolling1588BFInventory.edges_wrapG_qubits _ (generic_sites layout layout_widths layout_nodup cx cy) _
    (generic_free layout layout_widths layout_nodup cx cy 768 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 718 (by simp))
    (generic_free layout layout_widths layout_nodup cx cy 719 (by simp)) C cy
  intro i hi
  apply generic_free layout layout_widths layout_nodup cx cy i
  simp only [Q1591Resources.genericOmissions,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
  tauto

private theorem wrapper_facts (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Facts P Q) :
    toffoliCount (Edges.wrapper L C cy P)+144=toffoliCount (Edges.wrapper L C cy Q) ∧
    measurementCount (Edges.wrapper L C cy P)+54=measurementCount (Edges.wrapper L C cy Q) ∧
    gateSlots (Edges.wrapper L C cy P)≤gateSlots (Edges.wrapper L C cy Q) := by
  rcases h with ⟨ht,hm,hs,_⟩
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]
  exact ⟨by omega,by omega,by omega⟩

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2152325 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout layout_widths cx cy)).1
  have old:=ReflectionE1TickGap.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1499156 := by
  have diff:=(wrapper_facts layout (.some hc) cy _ _ (gen_facts layout layout_widths cx cy)).2.1
  have old:=ReflectionE1TickGap.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50166097 := by
  have diff:=(wrapper_facts layout C cy _ _ (gen_facts layout layout_widths cx cy)).2.2
  have old:=ReflectionE1TickGap.wrapper_slots C cx cy
  omega

end ECDSAAdd.Entrant.ReflectionE1TickGapLow48
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Low48Final =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.ReflectionE1Low48Generic

/-! E1/reflected Q1588 with TickGap tails and the Low48 square prefix. -/
namespace ECDSAAdd.Entrant.ReflectionE1TickGapLow48
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2152325,1499156,1588,50166097⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2152325 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1499156 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C) ≤ 1588 := by
  cases C with
  | zero => change qubits [] ≤ 1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50166097 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1499156
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50166097
    rw [normalize_slots];exact program_gateSlots C


end ECDSAAdd.Entrant.ReflectionE1TickGapLow48
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1

def sentinel : Nat := 115792089237316195423570985008687907853269984665640564039457584007908834671662
def sentinelHigh : Nat := 452312848583266388373324160190187140051835877600158453279131187530910662655

/-- Bits 1, 2, 5, 10..31 and 33..255 of `v`, packed in this order. -/
def probeVal (v : Nat) : Nat :=
  v / 2 % 4 + 4 * (v / 32 % 2) + 8 * (v / 1024 % 4194304) + 33554432 * (v / 8589934592)

theorem nonresidue_0 : ((115792089237316195423570985008687907853269984665640564039457584007908834671654 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem nonresidue_1 : ((115792089237316195423570985008687907853269984665640564039457584007908834671655 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem nonresidue_2 : ((115792089237316195423570985008687907853269984665640564039457584007908834671662 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem interval_nonresidue (n : Nat)
    (hn : n = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      n = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      n = 115792089237316195423570985008687907853269984665640564039457584007908834671662) :
    ((n : Fp)^3 + 7)^((p-1)/2) = -1 := by
  have hp : 115792089237316195423570985008687907853269984665640564039457584007908834671663 = p := by norm_num [p]
  have he : (p-1)/2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by norm_num [p]
  rw [he]
  have transport (q a : Nat) (hq : q = p)
      (h : ((a : ZMod q)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1) :
      ((a : Fp)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    subst q
    exact h
  rcases hn with rfl | rfl | rfl
  · exact transport _ _ hp nonresidue_0
  · exact transport _ _ hp nonresidue_1
  · exact transport _ _ hp nonresidue_2

theorem curve_x_not_interval {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    ¬ (x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      x.val = 115792089237316195423570985008687907853269984665640564039457584007908834671662) := by
  intro h
  have power := interval_nonresidue x.val h
  rw [ZMod.natCast_zmod_val] at power
  have eq := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at eq
  have square : y^2 = x^3+7 := by simpa [curve,curveA,curveB] using eq
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y ≠ 0 := by
    intro hz
    rw [← square,hz,zero_pow (by decide),zero_pow (by norm_num [p])] at power
    simp at power
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have even : p-1 = 2*((p-1)/2) := by norm_num [p]
  rw [even,pow_mul,square,power] at fermat
  have two : ((2 : Nat) : Fp) = 0 := by
    have sum : (-1 : Fp)+1 = 1+1 := by rw [fermat]
    rw [neg_add_cancel] at sum
    exact_mod_cast (by rw [sum]; norm_num : (2 : Fp) = 0)
  rw [ZMod.natCast_eq_zero_iff] at two
  norm_num [p] at two

theorem probe_cases (v : Nat)
    (hv : v < 115792089237316195423570985008687907853269984665640564039457584007908834671663)
    (h : probeVal v = sentinelHigh) :
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
      v = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
      v = 115792089237316195423570985008687907853269984665640564039457584007908834671662 := by
  unfold probeVal sentinelHigh at h
  omega

theorem curve_x_high_ne {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    probeVal x.val ≠ sentinelHigh := by
  intro h
  apply curve_x_not_interval hc
  have hv : x.val < 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
    have hp : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by norm_num [p]
    exact lt_of_lt_of_eq (ZMod.val_lt x) hp
  exact probe_cases x.val hv h

theorem sentinel_lt : sentinel < p := by norm_num [sentinel,p]
theorem sentinel_val : (sentinel : Fp).val = sentinel :=
  ZMod.val_natCast_of_lt sentinel_lt
theorem sentinel_ne_zero : (sentinel : Fp) ≠ 0 := by
  intro h
  have := congrArg ZMod.val h
  rw [sentinel_val,ZMod.val_zero] at this
  norm_num [sentinel] at this
theorem sentinel_high : probeVal sentinel = sentinelHigh := by
  unfold probeVal sentinel sentinelHigh
  norm_num

end ECDSAAdd.Entrant.FiniteFlagInterval
end

section
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic

theorem drop_sublist_drop (r : List Wire) (a b : Nat) (hab : a ≤ b) : (r.drop b).Sublist (r.drop a) := by
  have e : r.drop b = (r.drop a).drop (b - a) := by
    rw [List.drop_drop]; congr 1; omega
  rw [e]
  exact List.drop_sublist _ _

theorem seg_sublist (r rest : List Wire) (a k : Nat) (h : rest.Sublist (r.drop (a + k))) :
    ((r.drop a).take k ++ rest).Sublist (r.drop a) := by
  have e : (r.drop a).drop k = r.drop (a + k) := by
    rw [List.drop_drop]
  conv_rhs => rw [← List.take_append_drop k (r.drop a)]
  exact List.Sublist.append (List.Sublist.refl _) (e ▸ h)

theorem probe_sublist_gen (r : List Wire) :
    ((r.drop 1).take 2 ++ (r.drop 5).take 1 ++ (r.drop 10).take 22 ++ r.drop 33).Sublist r := by
  simp only [List.append_assoc]
  have hD : (r.drop 33).Sublist (r.drop (10 + 22)) := drop_sublist_drop r _ _ (by omega)
  have hC := seg_sublist r _ 10 22 hD
  have hB := seg_sublist r _ 5 1 ((hC).trans (drop_sublist_drop r _ _ (by omega)))
  have hA := seg_sublist r _ 1 2 ((hB).trans (drop_sublist_drop r _ _ (by omega)))
  exact hA.trans (List.drop_sublist _ _)

theorem probe_value_gen (r : List Wire) (hr : r.length = 256) (s : BasisState) :
    regValue ((r.drop 1).take 2 ++ (r.drop 5).take 1 ++ (r.drop 10).take 22 ++ r.drop 33) s =
      probeVal (regValue r s) := by
  have seg (a k : Nat) (h : a + k ≤ 256) :
      regValue ((r.drop a).take k) s = regValue r s / 2^a % 2^k := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by simp [hr]; omega),
      CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by omega)]
  have e1 := seg 1 2 (by norm_num)
  have e2 := seg 5 1 (by norm_num)
  have e3 := seg 10 22 (by norm_num)
  have e4 := CuccaroStreamedSquareWideLayout.regValue_drop_div r 33 (by omega) s
  simp only [Arithmetic.regValue_append, List.length_append, List.length_take, List.length_drop, hr,
    e1, e2, e3, e4, probeVal]
  norm_num

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalGadget =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires

def probeX (L : ControlledPointLayout) : List Wire :=
  (L.point.x.drop 1).take 2 ++ (L.point.x.drop 5).take 1 ++ (L.point.x.drop 10).take 22 ++ L.point.x.drop 33
def probeControl (L : ControlledPointLayout) : Wire := (probeX L).headD 0
def probeTail (L : ControlledPointLayout) : List Wire := (probeX L).tail
def zrep (L : ControlledPointLayout) : Program :=
  [.X L.point.finite] ++ maskedConstant L.point.finite L.point.x sentinel ++ [.X L.point.finite]
def clrF (L : ControlledPointLayout) : Program :=
  [.X L.point.finite] ++ equalConstant (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327

variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw in
theorem probe_length : (probeX L).length = 248 := by
  simp [probeX,show L.point.x.length = 256 from hw.inputX]
include hw in
theorem probe_cons : probeX L = probeControl L :: probeTail L := by
  have h := probe_length L hw
  unfold probeControl probeTail
  cases e : probeX L with
  | nil => simp [e] at h
  | cons a t => rfl
include hw in
theorem probeTail_length : (probeTail L).length = 247 := by
  simp [probeTail,probe_length L hw]
include hw in
theorem probeControl_mem : probeControl L ∈ L.point.x := by
  apply (probe_sublist_gen L.point.x).subset
  change probeControl L ∈ probeX L
  rw [probe_cons L hw]
  simp
theorem probeTail_mem (q : Wire) (hq : q ∈ probeTail L) : q ∈ L.point.x :=
  (probe_sublist_gen L.point.x).subset (show q ∈ probeX L from List.mem_of_mem_tail hq)
include hw in
theorem work_length : (L.dialogPool.take 247).length = 247 := by
  simp [L.dialogPool_length hw]
include hw hn in
theorem probe_nodup :
    (probeControl L :: L.point.finite :: probeTail L ++ L.dialogPool.take 247).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp := (List.take_sublist 247 L.dialogPool).count_le q
  have hx := (probe_sublist_gen L.point.x).count_le q
  have hc := congrArg (List.count q) (probe_cons L hw)
  simp only [dialogUsedWires,PointAddLayout.pointWires,List.count_append,List.count_cons,
    List.count_nil,List.cons_append] at h hc ⊢
  change (probeX L).count q ≤ L.point.x.count q at hx
  omega
include hw hn in
theorem finite_ne_probe : L.point.finite ≠ probeControl L := by
  intro h
  apply fin_not_x L hn
  rw [h]
  exact probeControl_mem L hw
include hw in
theorem probe_value_cons (s : BasisState) :
    regValue (probeX L) s = (if s (probeControl L) then 1 else 0) + 2*regValue (probeTail L) s := by
  conv_lhs => rw [probe_cons L hw]
  rfl
include hw in
theorem probe_value (s : BasisState) : regValue (probeX L) s = probeVal (regValue L.point.x s) :=
  probe_value_gen L.point.x hw.inputX s

include hw hn in
theorem clrF_run (s : State) (m : List Bool) (hz : regValue (L.dialogPool.take 247) s.basis = 0) :
    run (clrF L) m s = ⟨s.phase, writeBit s.basis L.point.finite
      (s.basis L.point.finite ^^ decide (regValue (probeX L) s.basis ≠ sentinelHigh))⟩ := by
  have nd := probe_nodup L hw hn
  have hfx := finite_ne_probe L hw hn
  have hft : L.point.finite ∉ (probeTail L) := by
    intro h; exact fin_not_x L hn (probeTail_mem L _ h)
  have hfp : L.point.finite ∉ L.dialogPool.take 247 := by
    intro h
    have hh := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) L.point.finite
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take h)
    simp only [dialogUsedWires, PointAddLayout.pointWires, List.count_append, List.count_cons,
      beq_self_eq_true, if_true] at hh
    omega
  let s1 : State := ⟨s.phase, writeBit s.basis L.point.finite (!s.basis L.point.finite)⟩
  have h1 : run [.X L.point.finite] [] s = s1 := rfl
  have hz1 : regValue (L.dialogPool.take 247) s1.basis = 0 := by
    rw [← hz]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hfp (e ▸ hq)
    simp [s1, writeBit, this]
  have hh := equalPorts_correct (probeControl L) L.point.finite (probeTail L) (L.dialogPool.take 247) 226156424291633194186662080095093570025917938800079226639565593765455331327
    ((probeTail_length L hw).trans (work_length L hw).symm) nd
    (by rw [probeTail_length L hw]; norm_num) s1 m hz1
  have hm0 : measurementCount [Instr.X L.point.finite] = 0 := rfl
  rw [clrF, run_append, hm0, List.take_zero, List.drop_zero, h1, hh]
  have e1 : s1.basis L.point.finite = !s.basis L.point.finite := by simp [s1, writeBit]
  have e2 : s1.basis (probeControl L) = s.basis (probeControl L) := by simp [s1, writeBit, Ne.symm hfx]
  have e3 : regValue (probeTail L) s1.basis = regValue (probeTail L) s.basis := by
    apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hft (e ▸ hq)
    simp [s1, writeBit, this]
  rw [e1, e2, e3, probe_value_cons L hw]
  congr 1
  funext q
  by_cases hq : q = L.point.finite
  · subst hq
    simp only [s1, writeBit, Function.update_self]
    cases s.basis L.point.finite <;> cases s.basis (probeControl L) <;>
      by_cases ht : regValue (probeTail L) s.basis = 226156424291633194186662080095093570025917938800079226639565593765455331327 <;> simp [ht,sentinelHigh] <;> omega
  · simp [s1, writeBit, Function.update_of_ne hq]

include hw hn in
theorem zrep_run (s : State) (m : List Bool) :
    (run (zrep L) m s).phase = s.phase ∧
    (∀ q, q ∉ L.point.x → (run (zrep L) m s).basis q = s.basis q) ∧
    regValue L.point.x (run (zrep L) m s).basis =
      regValue L.point.x s.basis ^^^ (if s.basis L.point.finite then 0 else sentinel) := by
  have hfx := fin_not_x L hn
  have hnd := finX_nodup L hn
  let s1 : State := ⟨s.phase, writeBit s.basis L.point.finite (!s.basis L.point.finite)⟩
  have h1 : run [.X L.point.finite] [] s = s1 := rfl
  have hm0 : measurementCount [Instr.X L.point.finite] = 0 := rfl
  have hmc := (maskedConstant_counts L.point.finite L.point.x sentinel).2
  have hk : sentinel < 2 ^ L.point.x.length := by
    rw [show L.point.x.length = 256 from hw.inputX]; norm_num [sentinel]
  obtain ⟨tp, tout, tx⟩ := maskedConstant_correct L.point.finite L.point.x sentinel hnd hfx hk s1 []
  obtain ⟨t, ht⟩ : ∃ t : State, t = run (maskedConstant L.point.finite L.point.x sentinel) [] s1 := ⟨_, rfl⟩
  rw [← ht] at tp tout tx
  have hrun : run (zrep L) m s = ⟨t.phase, writeBit t.basis L.point.finite (!t.basis L.point.finite)⟩ := by
    rw [zrep, run_append, run_append, measurementCount_append, hm0, hmc, Nat.add_zero,
      List.take_zero, List.drop_zero, List.take_nil, List.drop_nil, h1, ← ht]
    rfl
  have tf : t.basis L.point.finite = !s.basis L.point.finite := by
    rw [tout _ hfx]; simp [s1, writeBit]
  rw [hrun]
  refine ⟨tp, ?_, ?_⟩
  · intro q hq
    by_cases hqf : q = L.point.finite
    · subst hqf; simp [writeBit, tf]
    · simp only [writeBit, Function.update_of_ne hqf]
      rw [tout q hq]; simp [s1, writeBit, Function.update_of_ne hqf]
  · have e1 : regValue L.point.x (writeBit t.basis L.point.finite (!t.basis L.point.finite)) =
        regValue L.point.x t.basis := by
      apply regValue_congr; intro q hq
      have : q ≠ L.point.finite := fun e => hfx (e ▸ hq)
      simp [writeBit, this]
    have e2 : regValue L.point.x s1.basis = regValue L.point.x s.basis := by
      apply regValue_congr; intro q hq
      have : q ≠ L.point.finite := fun e => hfx (e ▸ hq)
      simp [s1, writeBit, this]
    show regValue L.point.x (writeBit t.basis L.point.finite (!t.basis L.point.finite)) = _
    rw [e1, tx, e2]
    have : s1.basis L.point.finite = !s.basis L.point.finite := by simp [s1, writeBit]
    rw [this]
    cases s.basis L.point.finite <;> rfl

include hw hn in
theorem clrF_step (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (clrF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))) := by
  intro s m v
  have hz : regValue (L.dialogPool.take 247) s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  rw [clrF_run L hw hn s m hz,probe_value L hw]
  have hfxy := finite_not_x L hn
  have hfs : s.basis L.point.finite = base L.point.finite := v.rest _ hfxy
  have hfx := fin_not_x L hn
  have hfy : L.point.finite ∉ L.point.y := fun h => hfxy (List.mem_append_right _ h)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show regValue L.point.x (writeBit s.basis L.point.finite _) = _
    rw [← v.x]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hfx (e ▸ hq)
    simp [writeBit, this]
  · show regValue L.point.y (writeBit s.basis L.point.finite _) = _
    rw [← v.y]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => hfy (e ▸ hq)
    simp [writeBit, this]
  · show writeBit s.basis L.point.finite _ L.core.generic = _
    simp [writeBit, Ne.symm (fin_ne_generic L hn), v.generic]
  · show regValue L.dialogPool (writeBit s.basis L.point.finite _) = _
    rw [← v.clean]; apply regValue_congr; intro q hq
    have : q ≠ L.point.finite := fun e => fin_not_pool L hn (e ▸ hq)
    simp [writeBit, this]
  · intro q hq
    show writeBit s.basis L.point.finite _ q = writeBit base L.point.finite _ q
    by_cases hqf : q = L.point.finite
    · subst hqf; simp [writeBit, hfs, v.x]
    · simp [writeBit, hqf, v.rest q hq]

include hw hn in
theorem zrep_step (X X' Y : Fp) (G : Bool) (base : BasisState)
    (hX : X'.val = X.val ^^^ (if base L.point.finite then 0 else sentinel)) :
    Triple (PointDialogValues L X Y G base) (zrep L) (PointDialogValues L X' Y G base) := by
  intro s m v
  obtain ⟨hp, hout, hx⟩ := zrep_run L hw hn s m
  have hf : s.basis L.point.finite = base L.point.finite := v.rest _ (finite_not_x L hn)
  refine ⟨hp, v.withX hn ?_ hout⟩
  rw [hx, v.x, hf, hX]

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalResources =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

include hw in
theorem ports_length : (zeroPorts (probeTail L) (L.dialogPool.take 247)).length = 247 := by
  have h := (zeroPorts_maps (probeTail L) (L.dialogPool.take 247)
    ((probeTail_length L hw).trans (work_length L hw).symm)).1
  simpa only [List.length_map,probeTail_length L hw] using congrArg List.length h

theorem zrep_counts : toffoliCount (zrep L) = 0 ∧ measurementCount (zrep L) = 0 := by
  have h := maskedConstant_counts L.point.finite L.point.x sentinel
  simp only [zrep,toffoliCount_append,measurementCount_append,h.1,h.2]
  exact ⟨rfl,rfl⟩

include hw in
theorem clrF_counts : toffoliCount (clrF L) = 247 ∧ measurementCount (clrF L) = 247 := by
  have h := equalConstant_counts (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327
  rw [ports_length L hw] at h
  simp only [clrF,toffoliCount_append,measurementCount_append,h.1,h.2]
  exact ⟨rfl,rfl⟩

include hn in
theorem zrep_physical : GatePhysical (zrep L) := by
  simp only [zrep,gatePhysical_append]
  refine ⟨⟨?_,maskedConstant_physical _ _ _ (fin_not_x L hn)⟩,?_⟩
  all_goals intro i hi; simp only [List.mem_singleton] at hi; subst hi; trivial

include hw hn in
theorem clrF_physical : GatePhysical (clrF L) := by
  have hl := (probeTail_length L hw).trans (work_length L hw).symm
  simp only [clrF,gatePhysical_append]
  refine ⟨?_,equalConstant_physical _ _ _ _ ?_⟩
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; trivial
  · exact (((zeroPorts_perm _ _ hl).cons _).cons _).nodup_iff.mpr (probe_nodup L hw hn)

include hw in
theorem old_clrF_support : wires (ECDSAAdd.Entrant.clrF L) =
    (L.point.finite :: (L.point.x ++ L.dialogPool.take 255)).toFinset := by
  have hl := (finTail_length L hw).trans (finWork255_length L hw).symm
  rw [ECDSAAdd.Entrant.clrF,wires_append,equalConstant_wires]
  ext q
  have hp : q ∈ (zeroPorts L.point.x.tail (L.dialogPool.take 255)).flatMap ZeroBit.wires ↔
      q ∈ L.point.x.tail ++ L.dialogPool.take 255 :=
    (zeroPorts_perm L.point.x.tail (L.dialogPool.take 255) hl).mem_iff
  have hx : q ∈ L.point.x ↔ q = x0 L ∨ q ∈ L.point.x.tail := by
    conv_lhs => rw [x_cons L hw]
    simp
  simp only [Finset.mem_union,wires,Instr.wires,Finset.union_empty,Finset.mem_singleton,
    List.mem_toFinset,List.mem_cons] at *
  rw [hp]
  simp only [List.mem_append] at *
  tauto

include hw in
theorem zrep_support_old : wires (zrep L) ⊆ wires (ECDSAAdd.Entrant.clrF L) := by
  rw [old_clrF_support L hw]
  intro q used
  simp only [zrep,wires_append,Finset.mem_union] at used
  rcases used with (h | h) | h
  · have eq : q = L.point.finite := by simpa [wires,Instr.wires] using h
    simp [eq]
  · have h' := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h)
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h' ⊢
    tauto
  · have eq : q = L.point.finite := by simpa [wires,Instr.wires] using h
    simp [eq]

include hw in
theorem clrF_support_old : wires (clrF L) ⊆ wires (ECDSAAdd.Entrant.clrF L) := by
  rw [old_clrF_support L hw]
  intro q used
  simp only [clrF,wires_append,Finset.mem_union] at used
  rcases used with h | h
  · have eq : q = L.point.finite := by simpa [wires,Instr.wires] using h
    simp [eq]
  · rw [equalConstant_wires] at h
    have h' := List.mem_toFinset.mp h
    rcases List.mem_cons.mp h' with e | h'
    · subst q
      simp [probeControl_mem L hw]
    rcases List.mem_cons.mp h' with e | h'
    · subst q; simp
    have hl := (probeTail_length L hw).trans (work_length L hw).symm
    rcases List.mem_append.mp ((zeroPorts_perm _ _ hl).subset h') with inp | work
    · simp [probeTail_mem L q inp]
    · have included : L.dialogPool.take 247 ⊆ L.dialogPool.take 255 := by
        have h : L.dialogPool.take 247 = (L.dialogPool.take 255).take 247 := by
          rw [List.take_take]; rfl
        rw [h]
        exact List.take_subset _ _
      simp [included work]

include hw in
theorem zrep_slots : gateSlots (zrep L) ≤ 258 := by
  have h := maskedConstant_gateSlots_le L.point.finite L.point.x sentinel
  rw [show L.point.x.length = 256 from hw.inputX] at h
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [zrep,gateSlots_append,one]
  omega

include hw in
theorem clrF_slots : gateSlots (clrF L) ≤ 2261 := by
  have h := equalConstant_gateSlots_le (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327
  rw [ports_length L hw] at h
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [clrF,gateSlots_append,one]
  omega

def constantSlots : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, k => (if k % 2 = 1 then 1 else 0) + constantSlots n (k/2)

theorem xor_slots_exact (r : List Wire) (k : Nat) :
    gateSlots (xorConstant r k) = constantSlots r.length k := by
  induction r generalizing k with
  | nil => rfl
  | cons w ws ih =>
    simp only [xorConstant,constantSlots,List.length_cons,gateSlots_append]
    split <;> simp [gateSlots_cons,instructionSlots,ih]

theorem masked_slots_exact (c : Wire) (r : List Wire) (k : Nat) :
    gateSlots (maskedConstant c r k) = constantSlots r.length k := by
  induction r generalizing k with
  | nil => rfl
  | cons w ws ih =>
    simp only [maskedConstant,constantSlots,List.length_cons,gateSlots_append]
    split <;> simp [gateSlots_cons,instructionSlots,ih]

theorem equal_slots_exact (c t : Wire) (bs : List ZeroBit) (k : Nat) :
    gateSlots (equalConstant c t bs k) = 7*bs.length+1+2*constantSlots bs.length k := by
  simp only [equalConstant,gateSlots_append,zeroControlled_gateSlots,xor_slots_exact,List.length_map]
  omega

include hw in
theorem zrep_slots_exact : gateSlots (zrep L) = 251 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [zrep,gateSlots_append,one,masked_slots_exact,
    show L.point.x.length = 256 from hw.inputX]
  decide +kernel

include hw in
theorem old_zrep_slots_exact : gateSlots (ECDSAAdd.Entrant.zrep L) = 4 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [ECDSAAdd.Entrant.zrep,gateSlots_append,one,masked_slots_exact,
    show L.point.x.length = 256 from hw.inputX]
  decide +kernel

include hw in
theorem clrF_slots_exact : gateSlots (clrF L) = 2225 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [clrF,gateSlots_append,one,equal_slots_exact,ports_length L hw]
  decide +kernel

include hw in
theorem old_clrF_slots_exact : gateSlots (ECDSAAdd.Entrant.clrF L) = 1789 := by
  have one : gateSlots [Instr.X L.point.finite] = 1 := rfl
  simp only [ECDSAAdd.Entrant.clrF,gateSlots_append,one,equal_slots_exact,finClr_ports_length L hw]
  decide +kernel

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalPoint =====
section
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

def clearF : Program := [.X L.point.finite] ++ MeasuredZeroClear.equalClear
  (probeControl L) L.point.finite (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327

include hw hn in
theorem clearF_eq (s : State) (m : List Bool) (hz : regValue (L.dialogPool.take 247) s.basis=0)
    (hzero : (run (clrF L) m s).basis L.point.finite=false) :
    run (clearF L) m s=run (clrF L) m s := by
  let bs := zeroPorts (probeTail L) (L.dialogPool.take 247)
  let s1 := run [Instr.X L.point.finite] [] s
  have hl := (probeTail_length L hw).trans (work_length L hw).symm
  have nd : (probeControl L::L.point.finite::bs.flatMap ZeroBit.wires).Nodup :=
    (((zeroPorts_perm _ _ hl).cons _).cons _).nodup_iff.mpr (probe_nodup L hw hn)
  have hz1 : ∀b∈bs,s1.basis b.work=false := by
    intro b hb
    have mem : b.work∈L.dialogPool.take 247 := by
      rw [←(zeroPorts_maps _ _ hl).2]
      exact List.mem_map.mpr ⟨b,hb,rfl⟩
    have ne : b.work≠L.point.finite := fun eq =>
      fin_not_pool L hn (eq ▸ List.mem_of_mem_take mem)
    simpa [s1,run,writeBit,ne] using (regValue_zero _ _).mp hz b.work mem
  have zero : (run (equalConstant (probeControl L) L.point.finite bs 226156424291633194186662080095093570025917938800079226639565593765455331327) m s1).basis
      L.point.finite=false := by
    simpa only [clrF,run_append,show measurementCount [Instr.X L.point.finite]=0 from rfl,
      List.take_zero,List.drop_zero] using hzero
  have eq := MeasuredZeroClear.equal_run_eq _ _ bs 226156424291633194186662080095093570025917938800079226639565593765455331327 nd s1 m hz1 zero
  simpa only [clearF,clrF,run_append,show measurementCount [Instr.X L.point.finite]=0 from rfl,
    List.take_zero,List.drop_zero] using eq

include hw hn in
theorem clearF_step (X Y : Fp) (G : Bool) (base : BasisState)
    (hf : base L.point.finite=decide (probeVal X.val ≠ sentinelHigh)) :
    Triple (PointDialogValues L X Y G base) (clearF L)
      (PointDialogValues L X Y G
        (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))) := by
  intro s m v
  have hz : regValue (L.dialogPool.take 247) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp v.clean q (List.mem_of_mem_take hq))
  have zero : (run (clrF L) m s).basis L.point.finite=false := by
    rw [clrF_run L hw hn s m hz,probe_value L hw,v.x]
    simp [writeBit,v.rest _ (finite_not_x L hn),hf]
  rw [clearF_eq L hw hn s m hz zero]
  exact clrF_step L hw hn X Y G base s m v

theorem clearF_support : wires (clearF L) ⊆ wires (clrF L) := by
  simp only [clearF,clrF,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (MeasuredZeroClear.equal_support _ _ _ _)

include hw in
theorem clearF_counts : toffoliCount (clearF L)=246 ∧ measurementCount (clearF L)=247 := by
  have h := MeasuredZeroClear.equal_counts (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327
  rw [ports_length L hw] at h
  simp only [clearF,toffoliCount_append,measurementCount_append,h.1,h.2]
  exact ⟨rfl,rfl⟩

include hw in
theorem clearF_slots : gateSlots (clearF L)=2221 := by
  have ne : zeroPorts (probeTail L) (L.dialogPool.take 247)≠[] := by
    intro h
    have len := ports_length L hw
    rw [h] at len
    contradiction
  have h := MeasuredZeroClear.equal_slots (probeControl L) L.point.finite
    (zeroPorts (probeTail L) (L.dialogPool.take 247)) 226156424291633194186662080095093570025917938800079226639565593765455331327 ne
  have old := clrF_slots_exact L hw
  simp only [clearF,clrF,gateSlots_append] at old ⊢
  omega

include hw hn in
theorem clearF_physical : GatePhysical (clearF L) := by
  have hl := (probeTail_length L hw).trans (work_length L hw).symm
  simp only [clearF,gatePhysical_append]
  refine ⟨?_,MeasuredZeroClear.equal_physical _ _ _ _ ?_⟩
  · intro i hi; simp only [List.mem_singleton] at hi; subst hi; trivial
  · exact (((zeroPorts_perm _ _ hl).cons _).cons _).nodup_iff.mpr (probe_nodup L hw hn)

end ECDSAAdd.Entrant.FiniteFlagInterval
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires
abbrev generic := ReflectionE1TickGapLow48.generic
def mid (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  clearF L ++ renameProgram (swapF L) (generic L cx cy) ++ clrF L
def gen (L : ControlledPointLayout) (cx cy : Fp) : Program := zrep L ++ mid L cx cy ++ zrep L
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn
theorem midFFused_values (cx cy : Fp) (X Y X' Y' : Fp) (G : Bool) (base : BasisState) (fin : Bool)
    (hP : ∀ base' : BasisState, Triple (PointDialogValues L X Y G base') (generic L cx cy)
      (PointDialogValues L X' Y' G base'))
    (hf : base L.point.finite = fin)
    (h1 : decide (probeVal X.val ≠ sentinelHigh) = fin) (h2 : decide (probeVal X'.val ≠ sentinelHigh) = fin) :
    Triple (PointDialogValues L X Y G base) (mid L cx cy) (PointDialogValues L X' Y' G base) := by
  have c1 := clearF_step L hw hn X Y G base (hf.trans h1.symm)
  have hb2 : (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
      L.point.finite = false := by
    simp [writeBit, hf, h1]
  have sw := swapF_values L hw hn (generic L cx cy) X Y X' Y' G _ hP hb2
  have c2 := clrF_step L hw hn X' Y' G
    (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
  have hb3 : writeBit (writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
      L.point.finite ((writeBit base L.point.finite (base L.point.finite ^^ decide (probeVal X.val ≠ sentinelHigh)))
        L.point.finite ^^ decide (probeVal X'.val ≠ sentinelHigh)) = base := by
    funext q
    by_cases hq : q = L.point.finite
    · subst hq; simp [writeBit, hf, h1, h2]
    · simp [writeBit, hq]
  rw [hb3] at c2
  exact (c1.seq sw).seq c2


theorem genFFused_ok {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (gen L cx cy) := by
  intro R b f hg s m v
  have hp := (point_holds _ _ _).mp v.point
  have hfinite : L.point.finite ∉ L.point.x ++ L.point.y := finite_not_x L hn
  have outside (q : Wire) (hq : q ∉ PointAddLayout.pointWires L.point) : q ∉ L.point.x ++ L.point.y := by
    simp only [PointAddLayout.pointWires,List.mem_append,List.mem_cons,not_or] at hq ⊢
    exact ⟨hq.1.2,hq.2⟩
  have hgen : s.basis L.core.generic = f L.core.generic := v.flags _ (by simp [inPlaceFlags])
  cases R with
  | zero =>
    have hG : f L.core.generic = false := by
      cases h : f L.core.generic
      · rfl
      · exact absurd rfl (hg h).1
    have values : PointDialogValues L 0 0 false s.basis s.basis :=
      ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
    have hfin : s.basis L.point.finite = false := hp.1
    have z1 := zrep_step L hw hn 0 (sentinel : Fp) 0 false s.basis (by rw [hfin, sentinel_val]; rfl)
    have mid := midFFused_values L hw hn cx cy (sentinel : Fp) 0 (sentinel : Fp) 0 false s.basis false
      (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn (sentinel : Fp) 0 cx cy base' sentinel_ne_zero) hfin
      (by rw [sentinel_val, sentinel_high]; decide) (by rw [sentinel_val, sentinel_high]; decide)
    have z2 := zrep_step L hw hn (sentinel : Fp) 0 0 false s.basis (by rw [hfin, sentinel_val]; rfl)
    obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
    refine ⟨phase, ?_⟩
    rw [hG]
    exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
      (fun q hq => hv.rest q (outside q hq))
  | @some x y hr =>
    have hfin : s.basis L.point.finite = true := hp.1
    have hx5 : decide (probeVal x.val ≠ sentinelHigh) = true := decide_eq_true (curve_x_high_ne hr)
    cases hG : f L.core.generic with
    | false =>
      have values : PointDialogValues L x y false s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y x y false s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_false L hw hn x y cx cy base' (curve_x_ne_zero hr)) hfin hx5 hx5
      have z2 := zrep_step L hw hn x x y false s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))
    | true =>
      have he := hg hG
      have den := dialog_denominators_ne_zero hr hc he.2.1 he.2.2.1 he.2.2.2
      have hg5 : decide (probeVal (genericX x y cx cy).val ≠ sentinelHigh) = true :=
        decide_eq_true (curve_x_high_ne (generic_nonsingular hr hc den.1))
      have values : PointDialogValues L x y true s.basis s.basis :=
        ⟨hp.2.1, hp.2.2, hgen.trans hG, v.clean, fun _ _ => rfl⟩
      have z1 := zrep_step L hw hn x x y true s.basis (by rw [hfin]; simp)
      have mid := midFFused_values L hw hn cx cy x y (genericX x y cx cy) (genericY x y cx cy) true s.basis true
        (fun base' => ReflectionE1TickGapLow48.generic_true L hw hn x y cx cy base' den.1 den.2) hfin hx5 hg5
      have z2 := zrep_step L hw hn (genericX x y cx cy) (genericX x y cx cy) (genericY x y cx cy) true
        s.basis (by rw [hfin]; simp)
      obtain ⟨phase, hv⟩ := ((z1.seq mid).seq z2) s m values
      refine ⟨phase, ?_⟩
      simp only [if_true, ← genericAdd_correct hr hc den.1, genericAdd]
      exact v.withPoint hn ((point_holds _ _ _).mpr ⟨(hv.rest _ hfinite).trans hp.1, hv.x, hv.y⟩)
        (fun q hq => hv.rest q (outside q hq))

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.FiniteFlagIntervalFinal =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FiniteFlagInterval
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots
  ReflectionE1TickGapLow48.generic

theorem gen_support_subset (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (gen L cx cy) ⊆ wires (ReflectionE1TickGapLow48.gen L cx cy) := by
  intro q used
  have hz : q ∈ wires (zrep L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => zrep_support_old L hw h
  have hc : q ∈ wires (clrF L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => clrF_support_old L hw h
  have he : q ∈ wires (clearF L) → q ∈ wires (ECDSAAdd.Entrant.clrF L) :=
    fun h => hc (clearF_support L h)
  simp only [gen,mid,ReflectionE1TickGapLow48.gen,ReflectionE1TickGapLow48.mid,
    generic,wires_append,Finset.mem_union] at used ⊢
  tauto

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy) ⊆ (OB5Support.genericSites L).toFinset :=
  (gen_support_subset L hw cx cy).trans (ReflectionE1TickGapLow48.gen_sites L hw hn cx cy)

theorem gen_counts (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+17 = toffoliCount (ReflectionE1TickGapLow48.gen L cx cy) ∧
    measurementCount (gen L cx cy)+16 = measurementCount (ReflectionE1TickGapLow48.gen L cx cy) ∧
    gateSlots (gen L cx cy) = gateSlots (ReflectionE1TickGapLow48.gen L cx cy)+1362 := by
  have z := zrep_counts L
  have c := clrF_counts L hw
  have e := clearF_counts L hw
  have oz := ECDSAAdd.Entrant.zrep_counts L
  have oc := ECDSAAdd.Entrant.clrF_counts L hw
  simp only [gen,mid,ReflectionE1TickGapLow48.gen,ReflectionE1TickGapLow48.mid,generic,
    toffoliCount_append,measurementCount_append,gateSlots_append,z.1,z.2,c.1,c.2,
    oz.1,oz.2,oc.1,oc.2,e.1,e.2,zrep_slots_exact L hw,clrF_slots_exact L hw,clearF_slots L hw,
    old_zrep_slots_exact L hw,old_clrF_slots_exact L hw]
  omega

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) := by
  have z := zrep_physical L hn
  have c := clrF_physical L hw hn
  have e := clearF_physical L hw hn
  have g := gatePhysical_rename (swapF L) (swapF_injective L hw hn) _
    (ReflectionE1TickGapLow48.generic_physical L hw hn cx cy)
  simpa only [gen,mid,gatePhysical_append,generic] using And.intro (And.intro z (And.intro (And.intro e g) c)) z

theorem wrapper_support_mono (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : wires P ⊆ wires Q) :
    wires (Edges.wrapper L C cy P) ⊆ wires (Edges.wrapper L C cy Q) := by
  simp only [Edges.wrapper,Edges.finiteProgram,wires_append,renameProgram_support]
  repeat' first
    | exact h
    | exact Finset.Subset.refl _
    | apply Finset.union_subset_union
    | apply Finset.image_subset_image

theorem wrapper_counts (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cx cy : Fp) :
    toffoliCount (Edges.wrapper L C cy (gen L cx cy))+17 =
      toffoliCount (Edges.wrapper L C cy (ReflectionE1TickGapLow48.gen L cx cy)) ∧
    measurementCount (Edges.wrapper L C cy (gen L cx cy))+16 =
      measurementCount (Edges.wrapper L C cy (ReflectionE1TickGapLow48.gen L cx cy)) ∧
    gateSlots (Edges.wrapper L C cy (gen L cx cy)) =
      gateSlots (Edges.wrapper L C cy (ReflectionE1TickGapLow48.gen L cx cy))+1362 := by
  have h := gen_counts L hw cx cy
  simp only [Edges.wrapper,Edges.finiteProgram,toffoliCount_append,measurementCount_append,
    gateSlots_append,renameProgram_counts,rename_gateSlots]
  omega

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 1588 := by
  have h := wrapper_support_mono layout C cy _ _ (gen_support_subset layout layout_widths cx cy)
  have card := Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)
  exact card.trans (ReflectionE1TickGapLow48.wrapper_qubits C cx cy)

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 2152308 := by
  have h := (wrapper_counts layout layout_widths (.some hc) cx cy).1
  have old := ReflectionE1TickGapLow48.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy)) ≤ 1499140 := by
  have h := (wrapper_counts layout layout_widths (.some hc) cx cy).2.1
  have old := ReflectionE1TickGapLow48.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy)) ≤ 50167459 := by
  have h := (wrapper_counts layout layout_widths C cx cy).2.2
  have old := ReflectionE1TickGapLow48.wrapper_slots C cx cy
  omega

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2152308,1499140,1588,50167459⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (genFFused_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2152308 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1499140 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C) ≤ 1588 := by
  cases C with
  | zero => change qubits [] ≤ 1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 50167459 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1499140
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 50167459
    rw [normalize_slots];exact program_gateSlots C

end ECDSAAdd.Entrant.FiniteFlagInterval
end

-- ===== ECDSAAdd.Submission.Entrant.Main =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.MeasuredDHFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      MeasuredDH.wrapper layout C cy (FiniteFlagInterval.gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2152302,1499138,1588,50167448⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := FiniteFlagInterval.gen_sites layout layout_widths layout_nodup cx cy
    have support := (MeasuredDH.wrapper_support layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ b R _
      (MeasuredDH.full_spec layout layout_widths layout_nodup R hc b _
        (FiniteFlagInterval.genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2152302 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have h := (MeasuredDH.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (MeasuredDH.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤2152302
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1499138 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have h := (MeasuredDH.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (MeasuredDH.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤1499138
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1588 := by
  cases C with
  | zero => change qubits []≤1588; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := MeasuredDH.wrapper_support layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (FiniteFlagInterval.wrapper_qubits (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact MeasuredDH.wrapper_physical layout layout_widths layout_nodup _ cy _
      (FiniteFlagInterval.gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50167448 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have h := (MeasuredDH.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    change gateSlots (MeasuredDH.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤50167448
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1499138
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1588
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50167448
    rw [normalize_slots]; exact program_gateSlots C
end ECDSAAdd.Entrant.MeasuredDHFinal
end

