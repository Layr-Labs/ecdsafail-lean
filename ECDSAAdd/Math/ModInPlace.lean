import ECDSAAdd.Arithmetic.Reduction
import ECDSAAdd.Math.HalvingBijection

namespace ECDSAAdd.Arithmetic

/-- 扩展源范围允许 A=p；一次约减后与源比较，恰好恢复减 p 时的借位。 -/
theorem modAddCore_cleanup (A Z p : Nat) (hA : A ≤ p) (hZ : Z < p) :
    (A + Z < p ↔ A ≤ (A + Z) % p) := by
  by_cases h : A + Z < p
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have hr : A + Z - p < p := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hr]
    omega

/-- 扩宽减 p 后，仅向低 n 位加回 p 即可约减；最高位暂时保留借位供比较清理。 -/
theorem modAddCore_low (t p n : Nat) (hp : 0 < p) (hpn : p < 2^n)
    (ht : t < 2*p) :
    let D := (t + 2^(n+1) - p) % 2^(n+1)
    (D % 2^n + (if t < p then p else 0)) % 2^n = t % p := by
  dsimp
  have hn : 0 < 2^n := by positivity
  rw [Nat.pow_succ]
  by_cases h : t < p
  · have hd : t + 2^n*2 - p = (t + 2^n - p) + 2^n := by omega
    have hb : t + 2^n*2 - p < 2^n*2 := by omega
    have hl : t + 2^n - p < 2^n := by omega
    rw [Nat.mod_eq_of_lt hb, hd, Nat.add_mod_right, Nat.mod_eq_of_lt hl,
      if_pos h, show t + 2^n - p + p = t + 2^n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h]
  · have hd : t + 2^n*2 - p = (t-p) + 2^n*2 := by omega
    have hl : t-p < 2^n := by omega
    have hb : t-p < 2^n*2 := by omega
    rw [hd, Nat.add_mod_right, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hl,
      if_neg h, Nat.add_zero, Nat.mod_eq_of_lt hl,
      Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- 取负源包装中的 p−A 仍在扩展源范围内，第二次取负恢复原源。 -/
theorem negRaw_range_restore (A p : Nat) (hA : A ≤ p) :
    p-A ≤ p ∧ p-(p-A) = A := by omega

/-- 将扩展源 p−A 加到规范目标上，就是自然数表示的模减。 -/
theorem modSubCore_value (A Z p : Nat) (hA : A ≤ p) :
    (Z + (p-A)) % p = (Z+p-A) % p := by
  congr 1
  omega

end ECDSAAdd.Arithmetic
