import ECDSAAdd.Arithmetic.MeasuredStreamedViews
import ECDSAAdd.Submission.Entrant.SquareGap

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem square_mod8 (M : Nat) : M^2%8≠5 ∧ M^2%8≠6 ∧ M^2%8≠7 := by
  have h : M^2%8=(M%8)^2%8 := Nat.pow_mod M 2 8
  have lt := Nat.mod_lt M (show 8>0 by norm_num)
  rw [h]
  interval_cases (M%8) <;> decide

/-- The 32-bit rotation of a 128-bit square is below the field modulus. -/
theorem rot32_canonical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hM : M<2^128) (hp : regValue L.core.product t=M^2) :
    regValue (rotateFull (L.core.product.take 256) 32) t*2^0<SquareReduction.p := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  rw [L.rotateFull_value hw t (M^2) hp 32 (by omega),Nat.mod_eq_of_lt hb]
  have m8 := square_mod8 M
  have e : M^2%2^(256-32)%8=M^2%8 := Nat.mod_mod_of_dvd _ (by norm_num)
  have hH : M^2/2^(256-32)<2^32 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc M^2<2^256 := hb
      _ = 2^32*2^(256-32) := by norm_num
  have hL := Nat.mod_lt (M^2) (show 2^(256-32)>0 by positivity)
  generalize M^2/2^(256-32)=H at hH ⊢
  generalize hX : M^2%2^(256-32)=X at hL e ⊢
  rw [←e] at m8
  norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c] at hH hL ⊢
  omega

/-- A finite bound on square gaps excludes the upper interval after rotation. -/
theorem rotation_canonical_of_gap (j D : Nat) (hj : j≤256)
    (threshold : SquareReduction.p/2^j+D=2^(256-j))
    (gap : ∀ M K : Nat, 0<K → K≤2^j → M^2<K*2^(256-j) →
      M^2+D<K*2^(256-j))
    (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hM : M<2^128) (hp : regValue L.core.product t=M^2) :
    regValue (rotateFull (L.core.product.take 256) j) t*2^0<SquareReduction.p := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  rw [L.rotateFull_value hw t (M^2) hp j hj,Nat.mod_eq_of_lt hb]
  simp only [Nat.pow_zero,Nat.mul_one]
  let A := 2^j
  let B := 2^(256-j)
  let H := M^2/B
  let X := M^2%B
  have ha : 0<A := Nat.two_pow_pos j
  have hB : 0<B := Nat.two_pow_pos (256-j)
  have prod : A*B=2^256 := by
    dsimp [A,B]
    rw [←pow_add,show j+(256-j)=256 by omega]
    rfl
  have high : H<A := by
    dsimp [H]
    rw [Nat.div_lt_iff_lt_mul hB,prod]
    exact hb
  have low : X<B := Nat.mod_lt _ hB
  have decomp : X+B*H=M^2 := Nat.mod_add_div _ B
  have upper : M^2<(H+1)*B := by
    calc M^2=X+B*H := decomp.symm
      _ < B+B*H := Nat.add_lt_add_right low _
      _ = (H+1)*B := by ring
  have next : H+1≤A := Nat.succ_le_iff.mpr high
  have separated := gap M (H+1) (Nat.succ_pos H) next upper
  change M^2+D<(H+1)*B at separated
  by_contra bad
  have rotated : SquareReduction.p≤H+A*X := Nat.le_of_not_gt bad
  have div : (H+A*X)/A=X := by
    rw [Nat.add_mul_div_left _ _ ha,Nat.div_eq_of_lt high,Nat.zero_add]
  have lower : SquareReduction.p/A≤(H+A*X)/A := Nat.div_le_div_right rotated
  rw [div] at lower
  change SquareReduction.p/A+D=B at threshold
  have near : B≤X+D := by omega
  have overlap : (H+1)*B≤M^2+D := by
    calc (H+1)*B=B*H+B := by ring
      _ ≤ B*H+(X+D) := Nat.add_le_add_left near _
      _ = M^2+D := by omega
  exact (Nat.not_le_of_gt separated) overlap

theorem rot4_canonical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hM : M<2^128) (hp : regValue L.core.product t=M^2) :
    regValue (rotateFull (L.core.product.take 256) 4) t*2^0<SquareReduction.p :=
  rotation_canonical_of_gap 4 268435518 (by decide) (by decide) square_gap4 L hw t M hM hp

theorem rot6_canonical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hM : M<2^128) (hp : regValue L.core.product t=M^2) :
    regValue (rotateFull (L.core.product.take 256) 6) t*2^0<SquareReduction.p :=
  rotation_canonical_of_gap 6 67108880 (by decide) (by decide) square_gap6 L hw t M hM hp

theorem rot10_canonical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (t : BasisState) (M : Nat) (hM : M<2^128) (hp : regValue L.core.product t=M^2) :
    regValue (rotateFull (L.core.product.take 256) 10) t*2^0<SquareReduction.p :=
  rotation_canonical_of_gap 10 4194305 (by decide) (by decide) square_gap10 L hw t M hM hp

end ECDSAAdd.Entrant
