import ECDSAAdd.Framework.Hoare
import Mathlib.Data.Nat.Bitwise

namespace ECDSAAdd.Arithmetic

/-- 小端读值相等恰好表示寄存器中的每一位相等。 -/
theorem regValue_eq_iff (r : List Wire) (s t : BasisState) :
    regValue r s = regValue r t ↔ ∀ w ∈ r, s w = t w := by
  constructor
  · intro h
    induction r with
    | nil => simp
    | cons a r ih =>
      have hb : s a = t a := by
        change (if s a then 1 else 0) + 2 * regValue r s =
          (if t a then 1 else 0) + 2 * regValue r t at h
        cases hs : s a <;> cases ht : t a <;>
          simp only [hs, ht, Bool.false_eq_true, if_false, if_true] at h ⊢ <;> omega
      have hr : regValue r s = regValue r t := by
        change (if s a then 1 else 0) + 2 * regValue r s =
          (if t a then 1 else 0) + 2 * regValue r t at h
        rw [hb] at h
        omega
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hb
      · exact ih hr w hw
  · intro h
    induction r with
    | nil => rfl
    | cons a r ih =>
      change (if s a then 1 else 0) + 2 * regValue r s =
        (if t a then 1 else 0) + 2 * regValue r t
      rw [h a (by simp), ih (fun w hw => h w (by simp [hw]))]

/-- XOR 按小端的最低位与高位分解。 -/
theorem xor_value_step (a b : Bool) (x y : Nat) :
    (a ^^ b).toNat + 2 * (x ^^^ y) = (a.toNat + 2 * x) ^^^ (b.toNat + 2 * y) := by
  have h := (Nat.xor_bit a x b y).symm
  cases a <;> cases b <;> simpa [Nat.bit, Bool.toNat, Nat.add_comm] using h

/-- 小端寄存器读取只依赖其自身线路。 -/
theorem regValue_congr (r : List Wire) (s t : BasisState)
    (h : ∀ w ∈ r, s w = t w) : regValue r s = regValue r t := by
  induction r with
  | nil => rfl
  | cons w ws ih =>
    change (if s w then 1 else 0) + 2 * regValue ws s =
      (if t w then 1 else 0) + 2 * regValue ws t
    rw [h w (by simp), ih (fun w hw => h w (by simp [hw]))]

/-- 零值恰好表示每一位均为 false。 -/
theorem regValue_zero (r : List Wire) (s : BasisState) :
    regValue r s = 0 ↔ ∀ w ∈ r, s w = false := by
  induction r with
  | nil => simp [regValue]
  | cons w ws ih =>
    change (if s w then 1 else 0) + 2 * regValue ws s = 0 ↔ _
    cases h : s w <;> simp [h, ih]

/-- n 位寄存器总是表示小于 2^n 的自然数。 -/
theorem regValue_lt (r : List Wire) (s : BasisState) : regValue r s < 2^r.length := by
  induction r with
  | nil => simp [regValue]
  | cons w ws ih =>
    change (if s w then 1 else 0) + 2 * regValue ws s < 2^(ws.length+1)
    rw [Nat.pow_succ]
    split <;> omega

/-- 对寄存器每根线路执行 X。 -/
def notRegister (r : List Wire) : Program := r.map Instr.X

/-- 寄存器内每一位取反，其他线路与相位保持。 -/
theorem notRegister_correct (r : List Wire) (hnd : r.Nodup) (s : State) (m : List Bool) :
    run (notRegister r) m s =
      ⟨s.phase, fun w => if w ∈ r then !s.basis w else s.basis w⟩ := by
  induction r generalizing s with
  | nil => simp [notRegister, run]
  | cons a r ih =>
    obtain ⟨ha, hr⟩ := List.nodup_cons.mp hnd
    simp only [notRegister, List.map_cons, run]
    rw [show List.map Instr.X r = notRegister r from rfl, ih hr]
    apply congrArg (State.mk s.phase)
    funext w
    by_cases hw : w = a
    · subst w; simp [writeBit, ha]
    · simp [writeBit, hw]

/-- 全位取反的读值为 2^n-1-X。 -/
theorem regValue_complement (r : List Wire) (s : BasisState) :
    regValue r (fun w => !s w) = 2^r.length - 1 - regValue r s := by
  have hsum : regValue r (fun w => !s w) + regValue r s + 1 = 2^r.length := by
    induction r with
    | nil => simp [regValue]
    | cons w ws ih =>
      change ((if !s w then 1 else 0) + 2 * regValue ws (fun w => !s w)) +
        ((if s w then 1 else 0) + 2 * regValue ws s) + 1 = 2^(ws.length+1)
      rw [Nat.pow_succ]
      cases s w <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
        if_true, if_false] <;> omega
  omega

/-- 全位取反的可读寄存器规格。 -/
theorem notRegister_spec (r : List Wire) (hnd : r.Nodup) (X : Nat) :
    {{ r = X }} notRegister r {{ r = (2^r.length - 1 - X) }} := by
  intro s m hP
  rw [notRegister_correct r hnd]
  refine ⟨rfl, ?_⟩
  change regValue r _ = _
  rw [regValue_congr r _ (fun w => !s.basis w) (by intro w hw; simp [hw]),
    regValue_complement]
  exact congrArg (2^r.length - 1 - ·) hP

/-- 全位取反只含 X 门，没有 Toffoli 或测量。 -/
theorem notRegister_counts (r : List Wire) :
    toffoliCount (notRegister r) = 0 ∧ measurementCount (notRegister r) = 0 := by
  induction r with
  | nil => exact ⟨rfl, rfl⟩
  | cons w ws ih => simpa [notRegister, toffoliCount, measurementCount] using ih

theorem notRegister_wires (r : List Wire) : wires (notRegister r) = r.toFinset := by
  induction r with
  | nil => rfl
  | cons w ws ih => simpa [notRegister, wires, Instr.wires] using congrArg (insert w) ih

/-- 互异寄存器的静态线路数就是位宽。 -/
theorem notRegister_qubitCount (r : List Wire) (hnd : r.Nodup) :
    qubitCount (notRegister r) = r.length := by
  rw [qubitCount, notRegister_wires, List.toFinset_card_of_nodup hnd]

/-- 小端寄存器第 i 位与自然数除法表示一致。 -/
theorem regValue_bit (r : List Wire) (i : Nat) (fallback : Wire) (s : BasisState) (hi : i<r.length) :
    (s (r.getD i fallback)).toNat=(regValue r s/2^i)%2 := by
  induction r generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => simp [regValue,Bool.toNat]; cases s a <;> simp
    | succ i =>
      simp only [List.getD_cons_succ]
      rw [ih i (by simpa using hi)]
      have hd : regValue (a::as) s/2=regValue as s := by
        change ((if s a then 1 else 0)+2*regValue as s)/2=regValue as s
        cases s a <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
      rw [Nat.pow_succ,Nat.mul_comm (2^i) 2,← Nat.div_div_eq_div_mul,hd]

end ECDSAAdd.Arithmetic
