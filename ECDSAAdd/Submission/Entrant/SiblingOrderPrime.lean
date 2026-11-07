import ECDSAAdd.Math.BitcoinPrimes
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.ReduceModChar

namespace ECDSAAdd.Entrant.SiblingOrder

open ECDSAAdd.Secp256k1

private theorem lucasFromFactors (n a : Nat) (factors : List Nat)
    (ha : (a : ZMod n) ^ (n - 1) = 1)
    (hn1 : n - 1 ≠ 0)
    (hprod : factors.prod = n - 1)
    (hprime : ∀ q ∈ factors, Nat.Prime q)
    (hpow : ∀ q ∈ factors, (a : ZMod n) ^ ((n - 1) / q) ≠ 1) :
    Nat.Prime n := by
  apply lucas_primality n (a : ZMod n) ha
  intro q hq hqdiv
  have hmemPF : q ∈ Nat.primeFactorsList (n - 1) :=
    (Nat.mem_primeFactorsList_iff_dvd hn1 hq).mpr hqdiv
  have hperm : List.Perm factors (Nat.primeFactorsList (n - 1)) :=
    Nat.primeFactorsList_unique hprod hprime
  exact hpow q (hperm.symm.mem_iff.mp hmemPF)

/-- Certificate subprime `13`. -/

private theorem prime_cert_01 : Nat.Prime 13 := by
  apply lucasFromFactors 13 2 [2, 2, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `17`. -/

private theorem prime_cert_02 : Nat.Prime 17 := by
  apply lucasFromFactors 17 3 [2, 2, 2, 2]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 := by simpa using hq
    rcases hcases with rfl
    · exact Nat.prime_two
  · intro q hq
    have hcases : q = 2 := by simpa using hq
    rcases hcases with rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `19`. -/

private theorem prime_cert_03 : Nat.Prime 19 := by
  apply lucasFromFactors 19 2 [2, 3, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `23`. -/

private theorem prime_cert_04 : Nat.Prime 23 := by
  apply lucasFromFactors 23 5 [2, 11]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_eleven
  · intro q hq
    have hcases : q = 2 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `29`. -/

private theorem prime_cert_05 : Nat.Prime 29 := by
  apply lucasFromFactors 29 2 [2, 2, 7]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `31`. -/

private theorem prime_cert_07 : Nat.Prime 37 := by
  apply lucasFromFactors 37 2 [2, 2, 3, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `41`. -/

private theorem prime_cert_08 : Nat.Prime 41 := by
  apply lucasFromFactors 41 6 [2, 2, 2, 5]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
  · intro q hq
    have hcases : q = 2 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `53`. -/

private theorem prime_cert_10 : Nat.Prime 59 := by
  apply lucasFromFactors 59 2 [2, 29]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 29 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_05
  · intro q hq
    have hcases : q = 2 ∨ q = 29 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `67`. -/

private theorem prime_cert_11 : Nat.Prime 67 := by
  apply lucasFromFactors 67 2 [2, 3, 11]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `73`. -/

private theorem prime_cert_12 : Nat.Prime 73 := by
  apply lucasFromFactors 73 5 [2, 2, 2, 3, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `83`. -/

private theorem prime_cert_14 : Nat.Prime 97 := by
  apply lucasFromFactors 97 5 [2, 2, 2, 2, 2, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `101`. -/

private theorem prime_cert_17 : Nat.Prime 109 := by
  apply lucasFromFactors 109 6 [2, 2, 3, 3, 3]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  · intro q hq
    have hcases : q = 2 ∨ q = 3 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `113`. -/

private theorem prime_cert_18 : Nat.Prime 113 := by
  apply lucasFromFactors 113 3 [2, 2, 2, 2, 7]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
  · intro q hq
    have hcases : q = 2 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `131`. -/

private theorem prime_cert_20 : Nat.Prime 149 := by
  apply lucasFromFactors 149 2 [2, 2, 37]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 37 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_07
  · intro q hq
    have hcases : q = 2 ∨ q = 37 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `199`. -/

private theorem prime_cert_21 : Nat.Prime 199 := by
  apply lucasFromFactors 199 3 [2, 3, 3, 11]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `239`. -/

private theorem prime_cert_24 : Nat.Prime 293 := by
  apply lucasFromFactors 293 2 [2, 2, 73]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 73 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_12
  · intro q hq
    have hcases : q = 2 ∨ q = 73 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `419`. -/

private theorem prime_cert_27 : Nat.Prime 461 := by
  apply lucasFromFactors 461 2 [2, 2, 5, 23]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 23 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_04
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 23 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `631`. -/

private theorem prime_cert_28 : Nat.Prime 631 := by
  apply lucasFromFactors 631 3 [2, 3, 3, 5, 7]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact Nat.prime_seven
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `797`. -/

private theorem prime_cert_29 : Nat.Prime 797 := by
  apply lucasFromFactors 797 2 [2, 2, 199]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 199 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_21
  · intro q hq
    have hcases : q = 2 ∨ q = 199 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `887`. -/

private theorem prime_cert_33 : Nat.Prime 1409 := by
  apply lucasFromFactors 1409 3 [2, 2, 2, 2, 2, 2, 2, 11]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_eleven
  · intro q hq
    have hcases : q = 2 ∨ q = 11 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `1627`. -/

private theorem prime_cert_35 : Nat.Prime 1871 := by
  apply lucasFromFactors 1871 14 [2, 5, 11, 17]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 11 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact Nat.prime_eleven
    · exact prime_cert_02
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 11 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `2011`. -/

private theorem prime_cert_36 : Nat.Prime 2011 := by
  apply lucasFromFactors 2011 3 [2, 3, 5, 67]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 67 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_cert_11
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 67 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `2621`. -/

private theorem prime_cert_39 : Nat.Prime 2731 := by
  apply lucasFromFactors 2731 3 [2, 3, 5, 7, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact Nat.prime_seven
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `2861`. -/

private theorem prime_cert_40 : Nat.Prime 2861 := by
  apply lucasFromFactors 2861 2 [2, 2, 5, 11, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 11 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact Nat.prime_eleven
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 11 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `4051`. -/

private theorem prime_cert_41 : Nat.Prime 4051 := by
  apply lucasFromFactors 4051 10 [2, 3, 3, 3, 3, 5, 5]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `4423`. -/

private theorem prime_cert_45 : Nat.Prime 9349 := by
  apply lucasFromFactors 9349 2 [2, 2, 3, 19, 41]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 19 ∨ q = 41 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_03
    · exact prime_cert_08
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 19 ∨ q = 41 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `13441`. -/

private theorem prime_cert_47 : Nat.Prime 16699 := by
  apply lucasFromFactors 16699 3 [2, 3, 11, 11, 23]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 23 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
    · exact prime_cert_04
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 23 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `20113`. -/

private theorem prime_cert_50 : Nat.Prime 28181 := by
  apply lucasFromFactors 28181 2 [2, 2, 5, 1409]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 1409 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_33
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 1409 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `41201`. -/

private theorem prime_cert_52 : Nat.Prime 85831 := by
  apply lucasFromFactors 85831 3 [2, 3, 5, 2861]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 2861 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_cert_40
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 2861 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `96557`. -/

private theorem prime_cert_54 : Nat.Prime 120233 := by
  apply lucasFromFactors 120233 3 [2, 2, 2, 7, 19, 113]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 19 ∨ q = 113 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact prime_cert_03
    · exact prime_cert_18
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 19 ∨ q = 113 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `305873`. -/

private theorem prime_cert_55 : Nat.Prime 305873 := by
  apply lucasFromFactors 305873 3 [2, 2, 2, 2, 7, 2731]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 2731 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact prime_cert_39
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 2731 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `1206781`. -/

private theorem prime_cert_57 : Nat.Prime 1627771 := by
  apply lucasFromFactors 1627771 3 [2, 3, 5, 29, 1871]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 29 ∨ q = 1871 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_cert_05
    · exact prime_cert_35
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 29 ∨ q = 1871 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `4681609`. -/

private theorem prime_cert_58 : Nat.Prime 4681609 := by
  apply lucasFromFactors 4681609 23 [2, 2, 2, 3, 97, 2011]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 97 ∨ q = 2011 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_14
    · exact prime_cert_36
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 97 ∨ q = 2011 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `7240687`. -/

private theorem prime_cert_61 : Nat.Prime 44706919 := by
  apply lucasFromFactors 44706919 6 [2, 3, 797, 9349]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 797 ∨ q = 9349 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_29
    · exact prime_cert_45
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 797 ∨ q = 9349 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `107590001`. -/

private theorem prime_cert_63 : Nat.Prime 545358713 := by
  apply lucasFromFactors 545358713 5 [2, 2, 2, 41, 59, 28181]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 41 ∨ q = 59 ∨ q = 28181 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_08
    · exact prime_cert_10
    · exact prime_cert_50
  · intro q hq
    have hcases : q = 2 ∨ q = 41 ∨ q = 59 ∨ q = 28181 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `297159362677`. -/

private theorem prime_cert_64 : Nat.Prime 297159362677 := by
  apply lucasFromFactors 297159362677 2 [2, 2, 3, 3, 11, 461, 1627771]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 461 ∨ q = 1627771 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
    · exact prime_cert_27
    · exact prime_cert_57
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 461 ∨ q = 1627771 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `107361793816595537`. -/

private theorem prime_cert_65 : Nat.Prime 107361793816595537 := by
  apply lucasFromFactors 107361793816595537 3 [2, 2, 2, 2, 16699, 85831, 4681609]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 16699 ∨ q = 85831 ∨ q = 4681609 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_47
    · exact prime_cert_52
    · exact prime_cert_58
  · intro q hq
    have hcases : q = 2 ∨ q = 16699 ∨ q = 85831 ∨ q = 4681609 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `173378833005251801`. -/

private theorem prime_cert_67 : Nat.Prime 174723607534414371449 := by
  apply lucasFromFactors 174723607534414371449 3 [2, 2, 2, 17, 59, 4051, 120233, 44706919]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 17 ∨ q = 59 ∨ q = 4051 ∨ q = 120233 ∨ q = 44706919 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_02
    · exact prime_cert_10
    · exact prime_cert_41
    · exact prime_cert_54
    · exact prime_cert_61
  · intro q hq
    have hcases : q = 2 ∨ q = 17 ∨ q = 59 ∨ q = 4051 ∨ q = 120233 ∨ q = 44706919 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `22149492674086928081353`. -/

private theorem prime_cert_70 : Nat.Prime 29047611873442575647497758179 := by
  apply lucasFromFactors 29047611873442575647497758179 2 [2, 293, 305873, 545358713, 297159362677]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 293 ∨ q = 305873 ∨ q = 545358713 ∨ q = 297159362677 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_24
    · exact prime_cert_55
    · exact prime_cert_63
    · exact prime_cert_64
  · intro q hq
    have hcases : q = 2 ∨ q = 293 ∨ q = 305873 ∨ q = 545358713 ∨ q = 297159362677 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `341948486974166000522343609283189`. -/

private theorem prime_cert_71 : Nat.Prime 341948486974166000522343609283189 := by
  apply lucasFromFactors 341948486974166000522343609283189 2 [2, 2, 3, 3, 3, 109, 29047611873442575647497758179]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 109 ∨ q = 29047611873442575647497758179 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_17
    · exact prime_cert_70
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 109 ∨ q = 29047611873442575647497758179 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide

/-- Certificate subprime `255515944373312847190720520512484175977`. -/

theorem order_prime : Nat.Prime order := by
  apply lucasFromFactors order 7 [2, 2, 2, 2, 2, 2, 3, 149, 631, 107361793816595537, 174723607534414371449, 341948486974166000522343609283189]
  · unfold order
    reduce_mod_char
  · unfold order
    norm_num
  · unfold order
    norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 149 ∨ q = 631 ∨ q = 107361793816595537 ∨ q = 174723607534414371449 ∨ q = 341948486974166000522343609283189 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_20
    · exact prime_cert_28
    · exact prime_cert_65
    · exact prime_cert_67
    · exact prime_cert_71
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 149 ∨ q = 631 ∨ q = 107361793816595537 ∨ q = 174723607534414371449 ∨ q = 341948486974166000522343609283189 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      unfold order
      reduce_mod_char
      decide

end ECDSAAdd.Entrant.SiblingOrder
