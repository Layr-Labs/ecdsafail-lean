import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring

namespace ECDSAAdd

/-- 奇模数下的标准代表元减半；奇数先加 p，避免非整数除法。 -/
def halveMod (p r : Nat) : Nat := if r%2 = 0 then r/2 else (r+p)/2

theorem halve_mod_bound (p r : Nat) (hp : p%2 = 1) (hr : r < p) : halveMod p r < p := by
  unfold halveMod
  split_ifs <;> omega

/-- 不依赖 p 为素数：两倍减半结果与原数模 p 相等。 -/
theorem halve_mod_correct (p r : Nat) (hp : p%2 = 1) :
    (2 : ZMod p)*(halveMod p r : Nat) = r := by
  unfold halveMod
  split_ifs with h
  · have he : 2*(r/2) = r := by omega
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using congrArg (fun n : Nat => (n : ZMod p)) he
  · have he : 2*((r+p)/2) = r+p := by omega
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, ZMod.natCast_self, add_zero] using
      congrArg (fun n : Nat => (n : ZMod p)) he

theorem halve_mod_iterate (p k r : Nat) (hp : p%2 = 1) (hr : r < p) :
    (halveMod p)^[k] r < p ∧
    (((halveMod p)^[k] r : Nat) : ZMod p)*2^k = r := by
  induction k with
  | zero => simp [hr]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨halve_mod_bound p _ hp ih.1, ?_⟩
    have hh := halve_mod_correct p ((halveMod p)^[k] r) hp
    rw [pow_succ]
    linear_combination (2 : ZMod p)^k * hh + ih.2

/-- 第二阶段固定展开，保留 k；第 i 轮由经典索引 i<k 决定是否减半。 -/
def halveFixed (p k : Nat) : Nat → Nat → Nat
  | 0, r => r
  | i+1, r => if i<k then halveMod p (halveFixed p k i r) else halveFixed p k i r

theorem halveFixed_eq (p k rounds r : Nat) :
    halveFixed p k rounds r = (halveMod p)^[min rounds k] r := by
  induction rounds with
  | zero => simp [halveFixed]
  | succ i ih =>
    rw [halveFixed, ih]
    split_ifs with h
    · rw [show min (i+1) k = min i k + 1 by omega, Function.iterate_succ_apply']
    · rw [show min (i+1) k = min i k by omega]

/-- k≤轮数时，恒等填充不改变 k 次模减半的结果。 -/
theorem halveFixed_correct (p k rounds r : Nat) (hp : p%2 = 1) (hr : r<p) (hk : k≤rounds) :
    halveFixed p k rounds r < p ∧
    (halveFixed p k rounds r : ZMod p)*2^k = r := by
  rw [halveFixed_eq, min_eq_right hk]
  exact halve_mod_iterate p k r hp hr

end ECDSAAdd

namespace ECDSAAdd

/-- 减半门列的值：奇数先加 p 再右移。 -/
theorem halveMod_eq (p r : Nat) : halveMod p r = (r + (if r % 2 = 1 then p else 0)) / 2 := by
  unfold halveMod
  split_ifs <;> omega

/-- 减半后由结果大小恢复原奇偶：r 奇 ⇔ 结果 ≥ (p+1)/2。 -/
theorem halve_parity (p r : Nat) (hp : p % 2 = 1) (hr : r < p) :
    r % 2 = 1 ↔ (p+1)/2 ≤ halveMod p r := by
  unfold halveMod
  split_ifs <;> omega

/-- 加倍门列的值与标志：r ≥ (p+1)/2 ⇔ 2r ≥ p；此时 2r mod p = 2r − p 且为奇数，否则 = 2r 为偶数。 -/
theorem double_flag (p r : Nat) (hp : p % 2 = 1) (hr : r < p) :
    ((p+1)/2 ≤ r ↔ p ≤ 2*r) ∧
    (2*r) % p = 2*r - (if (p+1)/2 ≤ r then p else 0) ∧
    (((2*r) % p) % 2 = 1 ↔ p ≤ 2*r) := by
  have h1 : (p+1)/2 ≤ r ↔ p ≤ 2*r := by omega
  have h2 : (2*r) % p = 2*r - (if (p+1)/2 ≤ r then p else 0) := by
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega), Nat.sub_zero]
  refine ⟨h1, h2, ?_⟩
  rw [h2]
  split_ifs <;> omega

end ECDSAAdd
