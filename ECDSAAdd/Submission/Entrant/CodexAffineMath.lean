import ECDSAAdd.Math.BitcoinPrimes

/-!
A 247-bit affine finite-point probe. The design follows the unintegrated
research direction in Yukon submission a67cb86c-fb4d-4634-98e9-dcb7b60d563a:
bits 1 and 2 agree; bit 5 and the selected high bits are set.
The case split and field proofs below are independently reconstructed.
-/
namespace ECDSAAdd.Entrant.CodexAffineMath
open Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

def matchesX (v : Nat) : Prop :=
  v / 2 % 2 = v / 4 % 2 ∧
  v / 32 % 2 = 1 ∧
  v / 1024 % 4194304 = 4194303 ∧
  v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607

instance : DecidablePred matchesX := fun v =>
  inferInstanceAs (Decidable (v / 2 % 2 = v / 4 % 2 ∧ v / 32 % 2 = 1 ∧
    v / 1024 % 4194304 = 4194303 ∧
    v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607))

def excluded (v : Nat) : Prop :=
  v = 115792089237316195423570985008687907853269984665640564039457584007908834671648 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671649 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671654 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671655 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671656 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671657 ∨
    v = 115792089237316195423570985008687907853269984665640564039457584007908834671662

theorem matches_cases (v : Nat) (hv : v < p) (h : matchesX v) : excluded v := by
  unfold matchesX at h
  unfold excluded
  norm_num [p] at hv
  omega

theorem sentinel_matches : matchesX (p-1) := by
  norm_num [matchesX,p]

private theorem nonresidue_0 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671648 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_1 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671649 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_2 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671654 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_3 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671655 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_4 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671656 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_5 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671657 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

private theorem nonresidue_6 :
    ((115792089237316195423570985008687907853269984665640564039457584007908834671662 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
  reduce_mod_char

theorem excluded_nonresidue (v : Nat) (hv : excluded v) :
    ((v : Fp)^3+7)^((p-1)/2) = -1 := by
  have hp : 115792089237316195423570985008687907853269984665640564039457584007908834671663 = p := by norm_num [p]
  have he : (p-1)/2 = 57896044618658097711785492504343953926634992332820282019728792003954417335831 := by norm_num [p]
  rw [he]
  have transport (q a : Nat) (hq : q=p)
      (h : ((a : ZMod q)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1) :
      ((a : Fp)^3+7)^57896044618658097711785492504343953926634992332820282019728792003954417335831 = -1 := by
    subst q
    exact h
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transport _ _ hp nonresidue_0
  · exact transport _ _ hp nonresidue_1
  · exact transport _ _ hp nonresidue_2
  · exact transport _ _ hp nonresidue_3
  · exact transport _ _ hp nonresidue_4
  · exact transport _ _ hp nonresidue_5
  · exact transport _ _ hp nonresidue_6

theorem curve_x_not_matches {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    ¬ matchesX x.val := by
  intro h
  haveI : NeZero p := ⟨by norm_num [p]⟩
  have power := excluded_nonresidue x.val (matches_cases x.val (ZMod.val_lt x) h)
  rw [ZMod.natCast_zmod_val] at power
  have equation := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at equation
  have square : y^2 = x^3+7 := by simpa [curve,curveA,curveB] using equation
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y≠0 := by
    intro hz
    rw [←square,hz,zero_pow (by decide),zero_pow (by norm_num [p])] at power
    simp at power
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have even : p-1=2*((p-1)/2) := by norm_num [p]
  rw [even,pow_mul,square,power] at fermat
  have ne : (-1 : Fp)≠1 := by decide
  exact ne fermat

theorem probe_bridge (a b : Bool) (rest v : Nat)
    (h : (if a then 1 else 0)+2*((if b then 1 else 0)+2*rest) =
      v / 2 % 4 + 4*(v / 32 % 2) + 8*(v / 1024 % 4194304) +
      33554432*(v / 8589934592)) :
    (!(b ^^ a) && decide (rest=2^246-1)) = decide (matchesX v) := by
  change (!(b ^^ a) && decide (rest=113078212145816597093331040047546785012958969400039613319782796882727665663)) = decide (matchesX v)
  have low : v / 2 % 4 = v / 2 % 2 + 2*(v / 4 % 2) := by
    have h4 : v / 2 / 2 = v / 4 := by simp [Nat.div_div_eq_div_mul]
    have h8 : v / 2 / 4 = v / 4 / 2 := by simp [Nat.div_div_eq_div_mul]
    omega
  have tail : rest = v / 32 % 2 + 2*(v / 1024 % 4194304) + 8388608*(v / 8589934592) := by
    have hlt := Nat.mod_lt (v / 2) (by decide : 0 < 4)
    cases a <;> cases b <;> simp_all only [Bool.false_eq_true, if_false, if_true] <;> omega
  have bits : (if a then 1 else 0) = v / 2 % 2 ∧ (if b then 1 else 0) = v / 4 % 2 := by
    cases a <;> cases b <;> simp_all only [Bool.false_eq_true, if_false, if_true] <;> omega
  have tail_iff : rest=113078212145816597093331040047546785012958969400039613319782796882727665663 ↔ v / 32 % 2 = 1 ∧ v / 1024 % 4194304 = 4194303 ∧ v / 8589934592 = 13479973333575319897333507543509815336818572211270286240551805124607 := by
    omega
  cases a <;> cases b <;> simp_all [matchesX] <;> omega

end ECDSAAdd.Entrant.CodexAffineMath

