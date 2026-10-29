import ECDSAAdd.Math.PointInPlace
import Mathlib.Tactic

namespace ECDSAAdd.Entrant
open Secp256k1

theorem seven_nonsquare (y : Fp) : y^2 ≠ 7 := by
  letI : Fact (Nat.Prime p) := ⟨p_prime⟩
  have hp : (7 : Fp)^((p-1)/2) = -1 := by
    unfold Fp p
    reduce_mod_char
  intro hy
  have hn : y ≠ 0 := by
    intro hz
    rw [hz] at hy
    have h7 : (7 : Fp) = 0 := by simpa using hy.symm
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd 7 p).mp h7
    norm_num [p] at hd
  have hf := ZMod.pow_card_sub_one_eq_one hn
  have he : 2*((p-1)/2) = p-1 := by norm_num [p]
  have heq : (7 : Fp)^((p-1)/2) = 1 := by
    rw [← hy, ← pow_mul, he]
    exact hf
  rw [hp] at heq
  have hz : (2 : Fp) = 0 := by linear_combination -heq
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp hz
  norm_num [p] at hd

theorem finite_x_nonzero {x y : Fp} (h : curve.toAffine.Nonsingular x y) : x ≠ 0 := by
  intro hx
  have he := h.1
  rw [curve.toAffine.equation_iff] at he
  have hy : y^2 = 7 := by simpa [hx, curve, curveA, curveB] using he
  exact seven_nonsquare y hy

def compressedCode (R : Point) : Nat :=
  ((coordinates R).getD (0,0)).1.val +
    2^256 * (((coordinates R).getD (0,0)).2.val % 2)

theorem compressedCode_lt (R : Point) : compressedCode R < 2^257 := by
  letI : NeZero p := ⟨by norm_num [p]⟩
  have hp : p < 2^256 := by norm_num [p]
  have hx := (ZMod.val_lt ((coordinates R).getD (0,0)).1).trans hp
  have hy := Nat.mod_lt ((coordinates R).getD (0,0)).2.val (show 0 < 2 by decide)
  dsimp only [compressedCode]
  omega

theorem parity_distinguishes_neg (y : Fp) (h : y.val % 2 = (-y).val % 2) :
    y = -y := by
  letI : NeZero p := ⟨by norm_num [p]⟩
  by_cases hy : y = 0
  · simp [hy]
  · letI : NeZero y := ⟨hy⟩
    rw [ZMod.val_neg_of_ne_zero] at h
    have hb := ZMod.val_lt y
    have hp : p % 2 = 1 := by norm_num [p]
    omega

theorem compressedCode_injective : Function.Injective compressedCode := by
  letI : NeZero p := ⟨by norm_num [p]⟩
  intro R C h
  have hp : p < 2^256 := by norm_num [p]
  have hx := (ZMod.val_lt ((coordinates R).getD (0,0)).1).trans hp
  have hc := (ZMod.val_lt ((coordinates C).getD (0,0)).1).trans hp
  have hv := h
  dsimp only [compressedCode] at hv
  have hxx : ((coordinates R).getD (0,0)).1 = ((coordinates C).getD (0,0)).1 := by
    apply ZMod.val_injective p
    omega
  have hyy : ((coordinates R).getD (0,0)).2.val % 2 =
      ((coordinates C).getD (0,0)).2.val % 2 := by
    rw [hxx] at hv
    omega
  cases R with
  | zero =>
    cases C with
    | zero => rfl
    | some hn =>
      simp only [coordinates, Option.getD_none, Option.getD_some] at hxx
      exact False.elim (finite_x_nonzero hn hxx.symm)
  | @some x y hn =>
    cases C with
    | zero =>
      simp only [coordinates, Option.getD_none, Option.getD_some] at hxx
      exact False.elim (finite_x_nonzero hn hxx)
    | @some u v hm =>
      simp only [coordinates, Option.getD_some] at hxx hyy
      rcases (sameX_iff_eq_or_neg hn hm).mp hxx with he | he
      · exact he
      · rw [WeierstrassCurve.Affine.Point.neg_some,
          WeierstrassCurve.Affine.Point.some.injEq] at he
        have hy : y = -v := by simpa only [negY_eq_neg] using he.2
        have hv : v = -v := parity_distinguishes_neg v (by simpa [hy] using hyy.symm)
        have hyv : y = v := hy.trans hv.symm
        subst u; subst v; rfl

end ECDSAAdd.Entrant
