import ECDSAAdd.Math.Kaliski
import ECDSAAdd.Math.ModularHalving
import ECDSAAdd.Math.BitcoinPrimes

namespace ECDSAAdd

/-- 数学层的固定轮数求逆函数，尚非可逆电路。负号先取模 p 的标准代表元。 -/
def kaliskiInverse (p a n : Nat) : Nat :=
  let z := kaliskiStep^[2*n] (kaliskiInit p a)
  halveFixed p z.k (2*n) (-(z.r : ZMod p)).val

/-- 对任意奇模数及与它互素的非零输入，第一阶段和固定减半阶段得到逆元。 -/
theorem kaliski_correct (p a n : Nat) (hpodd : p%2 = 1) (hp : p < 2^n)
    (ha0 : 0<a) (ha : a < 2^n) (hcop : p.Coprime a) :
    kaliskiInverse p a n = ((a : ZMod p)⁻¹).val := by
  have hp0 : 0<p := by omega
  letI : NeZero p := ⟨by omega⟩
  let z := kaliskiStep^[2*n] (kaliskiInit p a)
  have hi : KInvariant p a z := kaliski_iterate_invariant p a (2*n) _ (kaliski_init_invariant p a hp0 hcop)
  obtain ⟨_, hu, hk⟩ := kaliski_terminates p a n hp0 ha0 hp ha hcop
  change z.u = 1 at hu
  change z.k ≤ 2*n at hk
  let r := (-(z.r : ZMod p)).val
  have hr : r < p := ZMod.val_lt _
  obtain ⟨hout, hhalf⟩ := halveFixed_correct p z.k (2*n) r hpodd hr hk
  have hcast : (r : ZMod p) = -(z.r : ZMod p) := ZMod.natCast_zmod_val _
  rw [hcast] at hhalf
  have hscaled := hi.2.2.2.2.1
  rw [hu, Nat.cast_one, neg_one_mul] at hscaled
  have htwo : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).mpr (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hpodd))
  have hproduct : (a : ZMod p)*(halveFixed p z.k (2*n) r : Nat) = 1 := by
    apply (htwo.pow z.k).mul_left_inj.mp
    linear_combination (a : ZMod p)*hhalf - hscaled
  have haunit : IsUnit (a : ZMod p) := (ZMod.isUnit_iff_coprime a p).mpr hcop.symm
  have heq : (halveFixed p z.k (2*n) r : ZMod p) = (a : ZMod p)⁻¹ := by
    apply haunit.mul_left_inj.mp
    simpa only [mul_comm] using hproduct.trans (ZMod.mul_inv_of_unit (a : ZMod p) haunit).symm
  have hv := congrArg ZMod.val heq
  rw [ZMod.val_natCast_of_lt hout] at hv
  exact hv

/-- secp256k1 的数学求逆特例；fieldInverse 的电路规格通过本定理对接域逆元。 -/
theorem kaliski_inverse_p (a : Nat) (ha0 : 0<a) (ha : a<p) :
    kaliskiInverse p a 256 = ((a : Fp)⁻¹).val := by
  have hp : p < 2^256 := by norm_num [p]
  apply kaliski_correct p a 256 (by norm_num [p]) hp ha0 (ha.trans hp)
  apply Secp256k1.p_prime.coprime_iff_not_dvd.mpr
  intro hd
  exact (Nat.not_le_of_lt ha) (Nat.le_of_dvd ha0 hd)

end ECDSAAdd
