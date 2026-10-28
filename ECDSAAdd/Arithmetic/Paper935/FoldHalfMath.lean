import ECDSAAdd.Math.ModularHalving
import Mathlib.Tactic

namespace ECDSAAdd.Arithmetic.Paper935

/-- Value of subtracting a literal only in the low window, leaving the
high word untouched. The no-borrow event is an explicit numerical premise. -/
def windowSubtract (width k r : Nat) : Nat :=
  (r/2^width)*2^width+(r%2^width+2^width-k)%2^width

theorem windowSubtract_exact (width k r : Nat) (small : k<2^width)
    (noBorrow : k≤r%2^width) : windowSubtract width k r=r-k := by
  have bound := Nat.mod_lt r (Nat.two_pow_pos width)
  have decomp := Nat.mod_add_div r (2^width)
  unfold windowSubtract
  have sum : r%2^width+2^width-k=(r%2^width-k)+2^width := by omega
  rw [sum,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mul_comm (r/2^width)]
  omega

/-- Cyclic right rotation after the author's even fold correction. -/
def foldedHalf (n width c r : Nat) : Nat :=
  let v := if r%2=1 then windowSubtract width (c-1) r else r
  v/2+(v%2)*2^(n-1)

/-- On the explicit low-window no-borrow event, the author fold and rotation
implement exact modular halving for p=2^n-c. No probability bound is assumed. -/
theorem foldedHalf_correct (n width c r : Nat) (positive : 0<n)
    (cpos : 0<c) (csmall : c<2^n) (odd : c%2=1)
    (literal : c-1<2^width)
    (noBorrow : r%2=1 → c-1≤r%2^width) :
    foldedHalf n width c r=halveMod (2^n-c) r := by
  have power : 2^n=2*2^(n-1) := by
    conv_lhs => rw [show n=(n-1)+1 by omega]
    rw [pow_succ,Nat.mul_comm]
  unfold foldedHalf halveMod
  by_cases even : r%2=0
  · simp [even]
  · have rodd : r%2=1 := by omega
    rw [if_pos rodd,if_neg even,windowSubtract_exact width (c-1) r literal (noBorrow rodd)]
    have lower : c-1≤r := le_trans (noBorrow rodd) (Nat.mod_le r _)
    have parity : (r-(c-1))%2=1 := by omega
    dsimp only
    rw [parity,one_mul]
    omega

/-- The same successful fold preserves the canonical residue interval. -/
theorem foldedHalf_bound (n width c r : Nat) (positive : 0<n)
    (cpos : 0<c) (csmall : c<2^n) (odd : c%2=1)
    (literal : c-1<2^width) (range : r<2^n-c)
    (noBorrow : r%2=1 → c-1≤r%2^width) :
    foldedHalf n width c r<2^n-c := by
  rw [foldedHalf_correct n width c r positive cpos csmall odd literal noBorrow]
  have power : 2^n=2*2^(n-1) := by
    conv_lhs => rw [show n=(n-1)+1 by omega]
    rw [pow_succ,Nat.mul_comm]
  exact halve_mod_bound (2^n-c) r (by omega) range

end ECDSAAdd.Arithmetic.Paper935
