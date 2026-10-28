import ECDSAAdd.Math.Divsteps.Recovery

namespace ECDSAAdd.Divsteps

/-- Odd factorization gives the exact two-adic depth, including negative rows. -/
private theorem depth_of_odd_factor (n q : Int) (j : Nat)
    (hq : q % 2 = 1) (hn : n = 2 ^ j * q) : padicValInt 2 n = j := by
  subst hn
  rw [padicValInt.mul (by positivity) (by omega),
    padicValInt.eq_zero_of_not_dvd (p := 2) (z := q) (by push_cast; omega),
    add_zero, show ((2 : Int) ^ j) = ((2 ^ j : Nat) : Int) by push_cast; ring,
    padicValInt.of_nat, padicValNat.prime_pow]

theorem depth2_of_residue (n : Int) (h : n % 8 = 4) : padicValInt 2 n = 2 := by
  apply depth_of_odd_factor n (n / 4) 2
  · omega
  · norm_num
    omega

theorem depth3_of_residue (n : Int) (h : n % 16 = 8) : padicValInt 2 n = 3 := by
  apply depth_of_odd_factor n (n / 8) 3
  · omega
  · norm_num
    omega

theorem depth4_of_residue (n : Int) (h : n % 32 = 16) : padicValInt 2 n = 4 := by
  apply depth_of_odd_factor n (n / 16) 4
  · omega
  · norm_num
    omega

theorem depth2_of_bits (n : Int)
    (h0 : decide (bitk n 0 = 1) = false)
    (h1 : decide (bitk n 1 = 1) = false)
    (h2 : decide (bitk n 2 = 1) = true) : padicValInt 2 n = 2 := by
  apply depth2_of_residue
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at h0 h1 h2
  norm_num only [bitk, Nat.reduceAdd, Int.reducePow, Int.ediv_one] at h0 h1 h2
  omega

theorem depth3_of_bits (n : Int)
    (h0 : decide (bitk n 0 = 1) = false)
    (h1 : decide (bitk n 1 = 1) = false)
    (h2 : decide (bitk n 2 = 1) = false)
    (h3 : decide (bitk n 3 = 1) = true) : padicValInt 2 n = 3 := by
  apply depth3_of_residue
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at h0 h1 h2 h3
  norm_num only [bitk, Nat.reduceAdd, Int.reducePow, Int.ediv_one] at h0 h1 h2 h3
  omega

theorem depth4_of_bits (n : Int)
    (h0 : decide (bitk n 0 = 1) = false)
    (h1 : decide (bitk n 1 = 1) = false)
    (h2 : decide (bitk n 2 = 1) = false)
    (h3 : decide (bitk n 3 = 1) = false)
    (h4 : decide (bitk n 4 = 1) = true) : padicValInt 2 n = 4 := by
  apply depth4_of_residue
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at h0 h1 h2 h3 h4
  norm_num only [bitk, Nat.reduceAdd, Int.reducePow, Int.ediv_one] at h0 h1 h2 h3 h4
  omega

end ECDSAAdd.Divsteps
