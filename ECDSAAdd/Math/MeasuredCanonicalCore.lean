import ECDSAAdd.Math.ExactStreamedFold

namespace ECDSAAdd.Arithmetic

/-- The two disjoint reduction conditions combine by XOR, rather than
leaving two independent flags that would need separate predicate recovery. -/
theorem canonical_flag_bool (B c p X A : Nat)
    (hB : p+c=B) (hc : 0<c) (hX : X<p) (hA : A<p) :
    (decide (p≤(X+A)%B) ^^ decide (B≤X+A))=decide (p≤X+A) := by
  have h := exactFold_reduction_flag B c p X A hB hc hX hA
  by_cases q : B≤X+A <;> by_cases d : p≤(X+A)%B <;> by_cases r : p≤X+A <;>
    simp [q,d,r] at h ⊢

/-- The wide correction is exactly the canonical result plus one radix
when reduction was required. This proves both the output and the high flag. -/
theorem canonical_corrected_extended (B c p X A : Nat)
    (hB : p+c=B) (hX : X<p) (hA : A<p) :
    X+A+c*(if p≤X+A then 1 else 0)=
      (X+A)%p+B*(if p≤X+A then 1 else 0) := by
  by_cases small : X+A<p
  · rw [if_neg (by omega : ¬p≤X+A),Nat.mul_zero,Nat.mul_zero,Nat.add_zero,Nat.add_zero,
      Nat.mod_eq_of_lt small]
  · have mod : (X+A)%p=X+A-p := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    rw [if_pos (by omega : p≤X+A),Nat.mul_one,Nat.mul_one,mod]
    omega

theorem canonical_corrected_bound (B c p X A : Nat)
    (hB : p+c=B) (hc : 0<c) (hX : X<p) (hA : A<p) :
    X+A+c*(if p≤X+A then 1 else 0)<2*B := by
  rw [canonical_corrected_extended B c p X A hB hX hA]
  have hp : 0<p := by omega
  have mod := Nat.mod_lt (X+A) hp
  split_ifs <;> omega

end ECDSAAdd.Arithmetic
