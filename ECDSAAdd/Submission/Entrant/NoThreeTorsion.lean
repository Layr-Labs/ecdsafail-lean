import ECDSAAdd.Submission.Entrant.Prelude

namespace ECDSAAdd.Entrant.NoThreeTorsion
open Arithmetic Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

theorem negative21 :
    ((-21 : ZMod 115792089237316195423570985008687907853269984665640564039457584007908834671663)^
      57896044618658097711785492504343953926634992332820282019728792003954417335831)=-1 := by
  reduce_mod_char

theorem not_square (y : Fp) : y^2≠-21 := by
  intro sq
  have hp : p=115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
    norm_num [p]
  have h := negative21
  rw [←hp] at h
  change (-21 : Fp)^((p-1)/2)=-1 at h
  haveI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hy : y≠0 := by
    intro hz
    rw [hz] at sq
    norm_num at sq
    exact (by decide : (21 : Fp)≠0) sq
  have fermat := ZMod.pow_card_sub_one_eq_one hy
  have exp : p-1=2*((p-1)/2) := by norm_num [p]
  rw [exp,pow_mul,sq,h] at fermat
  have ne : (-1 : Fp)≠1 := by decide
  exact ne fermat

theorem double_x_ne {x y : Fp} (hc : curve.toAffine.Nonsingular x y) : doubleX x y≠x := by
  intro he
  have hyneg : y≠-y := of_decide_eq_true (cy_ne_neg hc)
  have hy : y≠0 := by intro hz; apply hyneg; simp [hz]
  have h2 : (2 : Fp)≠0 := by decide
  have h3 : (3 : Fp)≠0 := by decide
  have equation := hc.1
  rw [WeierstrassCurve.Affine.equation_iff] at equation
  have sq : y^2=x^3+7 := by simpa [curve,curveA,curveB] using equation
  unfold doubleX doubleSlope doubleNumerator doubleDenominator at he
  field_simp [hy] at he
  have product : 3*x*(x^3+28)=0 := by linear_combination -he - 12*x*sq
  have cubic := (mul_eq_zero.mp product).resolve_left (mul_ne_zero h3 (curve_x_ne_zero hc))
  apply not_square y
  linear_combination sq+cubic

theorem enabled {x y : Fp} (hc : curve.toAffine.Nonsingular x y) :
    exceptionBit (.some hc)=true := by
  classical
  let C : Point := .some hc
  have hy : y≠-y := of_decide_eq_true (cy_ne_neg hc)
  have hzero : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hdouble : C+C≠0 := by
    rw [show C+C=doublePoint hc hy from (doublePoint_correct hc hy).symm]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have hneg : C+C≠-C := by
    intro eq
    have e : (.some (double_nonsingular hc hy) : Point)=-C := by
      change doublePoint hc hy=-C
      rw [doublePoint_correct hc hy]
      exact eq
    exact double_x_ne hc ((sameX_iff_eq_or_neg (double_nonsingular hc hy) hc).mpr (Or.inr e))
  have hself : C+C≠C := by
    intro eq
    have e : C+C=C+0 := eq.trans (add_zero C).symm
    exact hzero (add_left_cancel e)
  have a : dialogExceptionPoint C≠0 := by
    intro eq
    exact hdouble (neg_eq_zero.mp eq)
  have b : dialogExceptionPoint C≠C := by
    intro eq
    exact hneg (neg_eq_iff_eq_neg.mp eq)
  have c : dialogExceptionPoint C≠-C := by
    intro eq
    exact hself (neg_injective eq)
  have pe (A B : Point) : pointEqual A B=decide (A=B) := by
    simp only [pointEqual,pointCode_injective.eq_iff]
  change exceptionBit C=true
  simp only [exceptionBit,pe]
  simp [a,b,c]

end ECDSAAdd.Entrant.NoThreeTorsion
