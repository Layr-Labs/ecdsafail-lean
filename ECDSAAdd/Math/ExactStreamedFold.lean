import ECDSAAdd.Math.ModInPlace
import ECDSAAdd.Math.SquareReduction
import Mathlib.Tactic.IntervalCases

namespace ECDSAAdd.Arithmetic

/-- A canonical sum's extended carry and trial comparison are disjoint.
Their sum is the single modular-reduction flag. -/
theorem exactFold_reduction_flag (B c p X A : Nat)
    (hB : p+c=B) (hc : 0<c) (hX : X<p) (hA : A<p) :
    (if B≤X+A then 1 else 0)+(if p≤(X+A)%B then 1 else 0)=
      (if p≤X+A then 1 else 0) := by
  by_cases h : X+A<B
  · rw [if_neg (by omega : ¬ B≤X+A),Nat.mod_eq_of_lt h]
    simp
  · have hmod : (X+A)%B=X+A-B := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    rw [hmod,if_pos (by omega : B≤X+A),if_neg (by omega : ¬p≤X+A-B),
      if_pos (by omega : p≤X+A)]

/-- Subtracting p in the extended word is equivalent to adding c in the low
word and toggling the extended high bit. The high bit finishes at zero. -/
theorem exactFold_low_and_top (B c p X A : Nat)
    (hB : p+c=B) (hc : 0<c) (hX : X<p) (hA : A<p) :
    let r := if p≤X+A then 1 else 0
    ((X+A)%B+c*r)%B=(X+A)%p ∧
    (if B≤X+A then 1 else 0)+((X+A)%B+c*r)/B=r := by
  dsimp
  have hp : 0<p := by omega
  have hb : 0<B := by omega
  by_cases small : X+A<p
  · rw [if_neg (by omega : ¬p≤X+A),Nat.mul_zero,Nat.add_zero,
      Nat.mod_eq_of_lt (by omega : X+A<B),Nat.mod_eq_of_lt small,
      Nat.mod_eq_of_lt (by omega : X+A<B),
      if_neg (by omega : ¬B≤X+A),Nat.div_eq_of_lt (by omega : X+A<B)]
    simp
  · have rmod : (X+A)%p=X+A-p := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    rw [if_pos (by omega : p≤X+A),Nat.mul_one,rmod]
    by_cases full : X+A<B
    · rw [Nat.mod_eq_of_lt full,if_neg (by omega : ¬B≤X+A)]
      have eq : X+A+c=(X+A-p)+B := by omega
      rw [eq,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega),
        Nat.add_div_right _ hb,Nat.div_eq_of_lt (by omega)]
      simp
    · have eq : (X+A)%B=X+A-B := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      rw [eq,if_pos (by omega : B≤X+A),
        Nat.mod_eq_of_lt (by omega : X+A-B+c<B),
        Nat.div_eq_of_lt (by omega : X+A-B+c<B)]
      constructor <;> omega

/-- The output/source comparison recovers the reduction flag for all
canonical operands; no truncated comparison or random-input assumption. -/
theorem exactFold_recover_flag (X A p : Nat) (hX : X<p) (hA : A<p) :
    ((X+A)%p<A ↔ p≤X+A) := by
  have h := modAddCore_cleanup A X p (by omega) hX
  rw [Nat.add_comm A X] at h
  omega

/-- The canonical reflection used to retain a common addition frame is an
involution, including both endpoints 0 and p-1. -/
theorem exactFold_reflection (p X : Nat) (hX : X<p) :
    p-1-X<p ∧ p-1-(p-1-X)=X := by omega

/-- Masking the source before the square is equivalent to controlling its
quadratic payload. -/
theorem exactFold_mask_square (enabled : Bool) (Y : Nat) :
    (if enabled then Y else 0)^2=if enabled then Y^2 else 0 := by
  cases enabled <;> simp

/-- No integer square has low three bits 111. -/
theorem exactFold_square_mod8 (Y : Nat) : Y^2%8≠7 := by
  have bound := Nat.mod_lt Y (by decide : 0<8)
  rw [Nat.pow_mod]
  interval_cases h : Y%8 <;> norm_num

/-- The unrotated 128-bit leaf square is already canonical. -/
theorem exactFold_leaf128_canonical (Y : Nat) (hY : Y<2^128) :
    Y^2<SquareReduction.p := by
  have hy : Y≤2^128-1 := by omega
  have hp : (2^128-1)^2<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  nlinarith

/-- Rotating a square's low 256 bits by 128 cannot enter [p,2^256):
that interval would require the square's low 128 bits to be all ones. -/
theorem exactFold_rotate128_canonical (Y : Nat) :
    (Y^2%2^256)/2^128+(Y^2%2^128)*2^128<SquareReduction.p := by
  let H : Nat := 2^128
  let P : Nat := Y^2%2^256
  have hh : 0<H := by norm_num [H]
  have hP : P<H*H := by
    have := Nat.mod_lt (Y^2) (by positivity : 0<2^256)
    norm_num [P,H] at *
    exact this
  have hi : P/H<H := by
    have := Nat.mod_add_div P H
    by_contra! bad
    have b := Nat.mul_le_mul_left H bad
    omega
  have hlo : Y^2%H<H := Nat.mod_lt _ hh
  have h8 : H%8=0 := by norm_num [H]
  have he : (Y^2%H)%8=Y^2%8 := by
    conv_rhs => rw [←Nat.mod_add_div (Y^2) H]
    simp [Nat.add_mod,Nat.mul_mod,h8]
  have hmax : Y^2%H≠H-1 := by
    intro bad
    have hres := exactFold_square_mod8 Y
    rw [←he,bad] at hres
    norm_num [H] at hres
  have hlt : Y^2%H≤H-2 := by omega
  have hp : H*H-H-1<SquareReduction.p := by
    norm_num [H,SquareReduction.p,SquareReduction.B,SquareReduction.c]
  change P/H+(Y^2%H)*H<SquareReduction.p
  have hi' : P/H≤H-1 := by omega
  have prod := Nat.mul_le_mul_right H hlt
  norm_num [H,SquareReduction.p,SquareReduction.B,SquareReduction.c] at *
  omega

end ECDSAAdd.Arithmetic
