import ECDSAAdd.Arithmetic.Registers

namespace ECDSAAdd.Arithmetic

/-- 经典常量按小端展开，只有常量位为 1 的线路才执行 X。 -/
def xorConstant : List Wire → Nat → Program
  | [], _ => []
  | w :: ws, k => (if k % 2 = 1 then [Instr.X w] else []) ++ xorConstant ws (k / 2)

/-- 异或经典常量，保持相位和寄存器外全部线路。 -/
theorem xorConstant_correct (r : List Wire) (hnd : r.Nodup) (k : Nat)
    (hk : k < 2^r.length) (s : State) (m : List Bool) :
    (run (xorConstant r k) m s).phase = s.phase ∧
    (∀ w, w ∉ r → (run (xorConstant r k) m s).basis w = s.basis w) ∧
    regValue r (run (xorConstant r k) m s).basis = regValue r s.basis ^^^ k := by
  induction r generalizing k s with
  | nil =>
    have hk0 : k = 0 := by simpa using hk
    simp [xorConstant, run, regValue, hk0]
  | cons w ws ih =>
    obtain ⟨hw, hn⟩ := List.nodup_cons.mp hnd
    have htail : k / 2 < 2^ws.length := by
      simp only [List.length_cons, Nat.pow_succ] at hk
      omega
    let s1 : State := if k % 2 = 1 then ⟨s.phase, writeBit s.basis w (!s.basis w)⟩ else s
    have hfirst : run (if k % 2 = 1 then [Instr.X w] else []) m s = s1 := by
      by_cases h : k % 2 = 1 <;> simp [h, run, s1]
    have hs1 : ∀ v, v ≠ w → s1.basis v = s.basis v := by
      intro v hv
      by_cases h : k % 2 = 1 <;> simp [s1, h, writeBit, hv]
    have hp1 : s1.phase = s.phase := by by_cases h : k % 2 = 1 <;> simp [s1, h]
    have hm : measurementCount (if k % 2 = 1 then [Instr.X w] else []) = 0 := by
      by_cases h : k % 2 = 1 <;> simp [h, measurementCount]
    let t := run (xorConstant ws (k/2)) m s1
    obtain ⟨hp, he, hv⟩ := ih hn (k/2) htail s1
    change t.phase = s1.phase at hp
    change ∀ v, v ∉ ws → t.basis v = s1.basis v at he
    change regValue ws t.basis = regValue ws s1.basis ^^^ (k/2) at hv
    rw [xorConstant, run_append, run_take, hm, List.drop_zero, hfirst]
    refine ⟨hp.trans hp1, ?_, ?_⟩
    · intro v hv
      have hv' : v ≠ w ∧ v ∉ ws := by simpa only [List.mem_cons, not_or] using hv
      exact (he v hv'.2).trans (hs1 v hv'.1)
    · have hreg : regValue ws s1.basis = regValue ws s.basis :=
        regValue_congr _ _ _ (fun v hv => hs1 v (by intro h; apply hw; simpa [h] using hv))
      have hbit : t.basis w = (s.basis w ^^ decide (k % 2 = 1)) := by
        rw [he w hw]
        by_cases h : k % 2 = 1 <;> simp [s1, h, writeBit]
      have hkbit : (decide (k % 2 = 1)).toNat + 2 * (k / 2) = k := by
        have hdiv := Nat.mod_add_div k 2
        have hmod := Nat.mod_lt k (by decide : 0 < 2)
        by_cases h : k % 2 = 1
        · simp only [h, decide_true, Bool.toNat_true]; omega
        · have hz : k % 2 = 0 := by omega
          simp only [h, decide_false, Bool.toNat_false]; omega
      change (if t.basis w then 1 else 0) + 2 * regValue ws t.basis = _
      rw [hbit, hv, hreg]
      have hxor := xor_value_step (s.basis w) (decide (k % 2 = 1))
        (regValue ws s.basis) (k/2)
      rw [hkbit] at hxor
      simpa only [regValue, List.foldr_cons, Bool.toNat, Bool.cond_eq_ite] using hxor

/-- 可重复使用同一常量程序载入和清理常量。 -/
theorem xorConstant_spec (r : List Wire) (hnd : r.Nodup) (k X : Nat) (hk : k < 2^r.length) :
    {{ r = X }} xorConstant r k {{ r = (X ^^^ k) }} := by
  intro s m hP
  obtain ⟨hp, _, hv⟩ := xorConstant_correct r hnd k hk s m
  exact ⟨hp, by simpa only [show regValue r s.basis = X from hP] using hv⟩

/-- 常量 XOR 不使用 Toffoli 或测量。 -/
theorem xorConstant_counts (r : List Wire) (k : Nat) :
    toffoliCount (xorConstant r k) = 0 ∧ measurementCount (xorConstant r k) = 0 := by
  induction r generalizing k with
  | nil => exact ⟨rfl, rfl⟩
  | cons w ws ih =>
    by_cases h : k % 2 = 1 <;>
      simp [xorConstant, h,
        toffoliCount, measurementCount, (ih (k/2)).1, (ih (k/2)).2]

/-- 常量 XOR 只触碰常量寄存器；实际支持集可能更小，因为 0 位不施门。 -/
theorem xorConstant_wires_subset (r : List Wire) (k : Nat) :
    wires (xorConstant r k) ⊆ r.toFinset := by
  induction r generalizing k with
  | nil => simp [xorConstant, wires]
  | cons w ws ih =>
    intro v hv
    by_cases h : k % 2 = 1
    · simp only [xorConstant, h, if_true, wires_append, wires, Instr.wires] at hv
      simp only [Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hv
      rcases hv with rfl | hv
      · simp
      · simpa only [List.toFinset_cons, Finset.mem_insert] using Or.inr (a := v = w) (ih (k/2) hv)
    · simp only [xorConstant, h, if_false, List.nil_append] at hv
      simpa only [List.toFinset_cons, Finset.mem_insert] using Or.inr (a := v = w) (ih (k/2) hv)

end ECDSAAdd.Arithmetic
