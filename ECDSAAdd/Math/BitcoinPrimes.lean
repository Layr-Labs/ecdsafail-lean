import ECDSAAdd.Math.BitcoinCurve
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.ReduceModChar

namespace ECDSAAdd
namespace Secp256k1

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


private theorem prime_cert_06 : Nat.Prime 31 := by
  apply lucasFromFactors 31 3 [2, 3, 5]
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


private theorem prime_cert_09 : Nat.Prime 53 := by
  apply lucasFromFactors 53 2 [2, 2, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


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


private theorem prime_cert_13 : Nat.Prime 83 := by
  apply lucasFromFactors 83 2 [2, 41]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 41 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_08
  · intro q hq
    have hcases : q = 2 ∨ q = 41 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


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


private theorem prime_cert_15 : Nat.Prime 101 := by
  apply lucasFromFactors 101 2 [2, 2, 5, 5]
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


private theorem prime_cert_16 : Nat.Prime 103 := by
  apply lucasFromFactors 103 5 [2, 3, 17]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_02
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_19 : Nat.Prime 131 := by
  apply lucasFromFactors 131 2 [2, 5, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_22 : Nat.Prime 239 := by
  apply lucasFromFactors 239 7 [2, 7, 17]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact prime_cert_02
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_23 : Nat.Prime 271 := by
  apply lucasFromFactors 271 6 [2, 3, 3, 3, 5]
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


private theorem prime_cert_25 : Nat.Prime 419 := by
  apply lucasFromFactors 419 2 [2, 11, 19]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 11 ∨ q = 19 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_eleven
    · exact prime_cert_03
  · intro q hq
    have hcases : q = 2 ∨ q = 11 ∨ q = 19 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_26 : Nat.Prime 443 := by
  apply lucasFromFactors 443 2 [2, 13, 17]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 13 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_01
    · exact prime_cert_02
  · intro q hq
    have hcases : q = 2 ∨ q = 13 ∨ q = 17 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_30 : Nat.Prime 887 := by
  apply lucasFromFactors 887 5 [2, 443]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 443 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_26
  · intro q hq
    have hcases : q = 2 ∨ q = 443 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_31 : Nat.Prime 971 := by
  apply lucasFromFactors 971 6 [2, 5, 97]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 97 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_14
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 97 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_32 : Nat.Prime 1373 := by
  apply lucasFromFactors 1373 2 [2, 2, 7, 7, 7]
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


private theorem prime_cert_34 : Nat.Prime 1627 := by
  apply lucasFromFactors 1627 3 [2, 3, 271]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 271 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_23
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 271 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_37 : Nat.Prime 2621 := by
  apply lucasFromFactors 2621 2 [2, 2, 5, 131]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 131 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_19
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 131 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_38 : Nat.Prime 2657 := by
  apply lucasFromFactors 2657 3 [2, 2, 2, 2, 2, 83]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 83 := by simpa using hq
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_13
  · intro q hq
    have hcases : q = 2 ∨ q = 83 := by simpa using hq
    rcases hcases with rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_42 : Nat.Prime 4423 := by
  apply lucasFromFactors 4423 3 [2, 3, 11, 67]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 67 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
    · exact prime_cert_11
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 67 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_43 : Nat.Prime 5323 := by
  apply lucasFromFactors 5323 5 [2, 3, 887]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 887 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_30
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 887 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_44 : Nat.Prime 7723 := by
  apply lucasFromFactors 7723 3 [2, 3, 3, 3, 11, 13]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_eleven
    · exact prime_cert_01
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 11 ∨ q = 13 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_46 : Nat.Prime 13441 := by
  apply lucasFromFactors 13441 11 [2, 2, 2, 2, 2, 2, 2, 3, 5, 7]
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


private theorem prime_cert_48 : Nat.Prime 20113 := by
  apply lucasFromFactors 20113 10 [2, 2, 2, 2, 3, 419]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 419 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_25
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 419 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_49 : Nat.Prime 24809 := by
  apply lucasFromFactors 24809 6 [2, 2, 2, 7, 443]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 443 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact prime_cert_26
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 443 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_51 : Nat.Prime 41201 := by
  apply lucasFromFactors 41201 3 [2, 2, 2, 2, 5, 5, 103]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 103 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_16
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 103 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_53 : Nat.Prime 96557 := by
  apply lucasFromFactors 96557 2 [2, 2, 101, 239]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 101 ∨ q = 239 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact prime_cert_15
    · exact prime_cert_22
  · intro q hq
    have hcases : q = 2 ∨ q = 101 ∨ q = 239 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_56 : Nat.Prime 1206781 := by
  apply lucasFromFactors 1206781 10 [2, 2, 3, 5, 20113]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 20113 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_cert_48
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 20113 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_59 : Nat.Prime 7240687 := by
  apply lucasFromFactors 7240687 3 [2, 3, 1206781]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 1206781 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_56
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 1206781 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_60 : Nat.Prime 13331831 := by
  apply lucasFromFactors 13331831 13 [2, 5, 971, 1373]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 971 ∨ q = 1373 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_31
    · exact prime_cert_32
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 971 ∨ q = 1373 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_62 : Nat.Prime 107590001 := by
  apply lucasFromFactors 107590001 3 [2, 2, 2, 2, 5, 5, 5, 5, 7, 29, 53]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 7 ∨ q = 29 ∨ q = 53 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact Nat.prime_seven
    · exact prime_cert_05
    · exact prime_cert_09
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 7 ∨ q = 29 ∨ q = 53 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_66 : Nat.Prime 173378833005251801 := by
  apply lucasFromFactors 173378833005251801 6 [2, 2, 2, 5, 5, 2621, 24809, 13331831]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 2621 ∨ q = 24809 ∨ q = 13331831 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_five
    · exact prime_cert_37
    · exact prime_cert_49
    · exact prime_cert_60
  · intro q hq
    have hcases : q = 2 ∨ q = 5 ∨ q = 2621 ∨ q = 24809 ∨ q = 13331831 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_68 : Nat.Prime 22149492674086928081353 := by
  apply lucasFromFactors 22149492674086928081353 5 [2, 2, 2, 3, 5323, 173378833005251801]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5323 ∨ q = 173378833005251801 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_43
    · exact prime_cert_66
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5323 ∨ q = 173378833005251801 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_69 : Nat.Prime 132896956044521568488119 := by
  apply lucasFromFactors 132896956044521568488119 6 [2, 3, 22149492674086928081353]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 22149492674086928081353 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact prime_cert_68
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 22149492674086928081353 := by simpa using hq
    rcases hcases with rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_72 : Nat.Prime 255515944373312847190720520512484175977 := by
  apply lucasFromFactors 255515944373312847190720520512484175977 3 [2, 2, 2, 7, 7, 11, 1627, 2657, 4423, 41201, 96557, 7240687, 107590001]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 11 ∨ q = 1627 ∨ q = 2657 ∨ q = 4423 ∨ q = 41201 ∨ q = 96557 ∨ q = 7240687 ∨ q = 107590001 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_seven
    · exact Nat.prime_eleven
    · exact prime_cert_34
    · exact prime_cert_38
    · exact prime_cert_42
    · exact prime_cert_51
    · exact prime_cert_53
    · exact prime_cert_59
    · exact prime_cert_62
  · intro q hq
    have hcases : q = 2 ∨ q = 7 ∨ q = 11 ∨ q = 1627 ∨ q = 2657 ∨ q = 4423 ∨ q = 41201 ∨ q = 96557 ∨ q = 7240687 ∨ q = 107590001 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


private theorem prime_cert_73 : Nat.Prime 205115282021455665897114700593932402728804164701536103180137503955397371 := by
  apply lucasFromFactors 205115282021455665897114700593932402728804164701536103180137503955397371 10 [2, 3, 5, 29, 29, 31, 7723, 132896956044521568488119, 255515944373312847190720520512484175977]
  · reduce_mod_char
  · norm_num
  · norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 29 ∨ q = 31 ∨ q = 7723 ∨ q = 132896956044521568488119 ∨ q = 255515944373312847190720520512484175977 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_cert_05
    · exact prime_cert_06
    · exact prime_cert_44
    · exact prime_cert_69
    · exact prime_cert_72
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 29 ∨ q = 31 ∨ q = 7723 ∨ q = 132896956044521568488119 ∨ q = 255515944373312847190720520512484175977 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      reduce_mod_char
      decide


theorem p_prime : Nat.Prime p := by
  apply lucasFromFactors p 3 [2, 3, 7, 13441, 205115282021455665897114700593932402728804164701536103180137503955397371]
  · unfold p
    reduce_mod_char
  · unfold p
    norm_num
  · unfold p
    norm_num
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 13441 ∨ q = 205115282021455665897114700593932402728804164701536103180137503955397371 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_seven
    · exact prime_cert_46
    · exact prime_cert_73
  · intro q hq
    have hcases : q = 2 ∨ q = 3 ∨ q = 7 ∨ q = 13441 ∨ q = 205115282021455665897114700593932402728804164701536103180137503955397371 := by simpa using hq
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals
      unfold p
      reduce_mod_char
      decide

/-- The fixed secp256k1 base field, derived without exporting the raw primality `Fact`. -/
instance certifiedFpField : Field Fp := by
  letI : Fact (Nat.Prime p) := ⟨p_prime⟩
  infer_instance

/-- The fixed secp256k1 curve is elliptic over the certified base field. -/
instance certifiedCurveIsElliptic : curve.IsElliptic := by
  exact ⟨isUnit_iff_ne_zero.mpr curve_discriminant_ne_zero⟩

end Secp256k1
end ECDSAAdd
