import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ECDSAAdd.Arithmetic

/-- Peel the low bit of an integer square. The cross term starts two bits higher. -/
theorem square_bit_step (b : Bool) (Y : Nat) :
    (b.toNat + 2 * Y)^2 = b.toNat + 4 * Y^2 + 4 * b.toNat * Y := by
  cases b <;> simp <;> ring

/-- An m-bit natural has a square fitting in 2m bits, including the empty word. -/
theorem square_bound (X m : Nat) (hX : X < 2^m) : X^2 < 2^(2*m) := by
  have hh : X * X < 2^m * 2^m := Nat.mul_self_lt_mul_self hX
  simpa [pow_two, ← Nat.pow_add, ← two_mul] using hh

/-- The sum of two 128-bit words needs 129 bits. -/
theorem square_sum128_bound (L H : Nat) (hL : L < 2^128) (hH : H < 2^128) :
    L + H < 2^129 := by
  norm_num at hL hH ⊢
  omega

/-- The square of that sum needs 258 bits, rather than 256. -/
theorem square_sum128_square_bound (L H : Nat)
    (hL : L < 2^128) (hH : H < 2^128) : (L + H)^2 < 2^258 := by
  simpa only [show 2 * 129 = 258 by omega] using
    square_bound (L + H) 129 (square_sum128_bound L H hL hH)

/-- Division-free Karatsuba identity, stated with additions to avoid truncated subtraction. -/
theorem square_karatsuba (L H R : Nat) :
    (L + R * H)^2 + R * L^2 + R * H^2 =
      L^2 + R * (L + H)^2 + R^2 * H^2 := by
  ring

/-- The 128/128 split used by the 256-bit square circuit. -/
theorem square_karatsuba128 (L H : Nat) :
    (L + 2^128 * H)^2 + 2^128 * L^2 + 2^128 * H^2 =
      L^2 + 2^128 * (L + H)^2 + 2^256 * H^2 := by
  simpa only [← Nat.pow_mul, show 128 * 2 = 256 by omega] using
    square_karatsuba L H (2^128)

/-- The mathematical cross term is nonnegative before reducing modulo the word size. -/
theorem square_cross (L H : Nat) : (L + H)^2 - L^2 - H^2 = 2 * L * H := by
  have h : (L + H)^2 = L^2 + H^2 + 2 * L * H := by ring
  omega

/-- The high-word update of one triangular row fits its 2k-bit target. -/
theorem square_row_bound (b : Bool) (Y k : Nat) (hY : Y < 2^k) :
    Y^2 + (if b then Y else 0) < 2^(2*k) := by
  have hp : 0 < 2^k := by positivity
  have he : 2^(2*k) = (2^k)^2 := by rw [Nat.mul_comm 2 k, Nat.pow_mul]
  rw [he]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  · nlinarith
  · nlinarith

/-- Equivalent row-oriented form, matching the two low output bits. -/
theorem square_bit_row (b : Bool) (Y : Nat) :
    (b.toNat + 2 * Y)^2 = b.toNat + 4 * (Y^2 + (if b then Y else 0)) := by
  cases b <;> simp <;> ring

end ECDSAAdd.Arithmetic
