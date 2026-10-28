import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ECDSAAdd.Arithmetic.SquareReduction

def B : Nat := 2^256
def c : Nat := 2^32 + 977
def p : Nat := B-c

/-- 带进位的第三折叠落在 p 以下。 -/
theorem small_carry_bound : c*c+c-1<p := by norm_num [c,p,B]

/-- 第一折叠的高字至多为 c。 -/
theorem first_high_bound (l h : Nat) (hl : l<B) (hh : h<B) :
    (l+c*h)/B ≤ c := by
  have hb : 0<B := by norm_num [B]
  apply (Nat.div_le_iff_le_mul_add_pred hb).2
  norm_num [B,c] at *
  omega

/-- 第一折叠完整值放入 289 位。 -/
theorem first_bound (l h : Nat) (hl : l<B) (hh : h<B) : l+c*h<2^289 := by
  rw [show 289=256+33 by omega, Nat.pow_add]
  norm_num [B,c] at *
  omega

/-- 参数化的伪梅森折叠保持模 p 余数。 -/
theorem fold_mod (n : Nat) : (n%B+c*(n/B))%p=n%p := by
  have hb : B=p+c := by norm_num [B,p,c]
  have he : n = n%B+B*(n/B) := (Nat.mod_add_div n B).symm
  have ha : n%B+B*(n/B) = (n%B+c*(n/B))+p*(n/B) := by rw [hb]; ring
  conv_rhs => rw [he,ha]
  simp

/-- 第一折叠值同原来的双字整数同余。 -/
theorem first_mod (l h : Nat) : (l+c*h)%p=(l+B*h)%p := by
  have hb : B=p+c := by norm_num [B,p,c]
  have he : l+B*h=(l+c*h)+p*h := by rw [hb]; ring
  rw [he]
  simp

/-- 第二折叠值只需要一位高进位。 -/
theorem second_bound (l h : Nat) (hl : l<B) (hh : h<B) :
    (l+c*h)%B+c*((l+c*h)/B)<2*B := by
  have hq := first_high_bound l h hl hh
  have hr := Nat.mod_lt (l+c*h) (show 0<B by norm_num [B])
  have hc : c*c<B := by norm_num [c,B]
  nlinarith

/-- 两倍字长以内的值，其最高字是布尔进位。 -/
theorem carry_bound (v : Nat) (hv : v<2*B) : v/B≤1 := by
  have hb : 0<B := by norm_num [B]
  have h := (Nat.div_lt_iff_lt_mul hb).2 hv
  omega

/-- 有进位时，第三折叠落在很小的规范区间内。 -/
theorem third_carry_bound (v : Nat) (hv : v≤B-1+c*c) (hb : v/B=1) :
    v%B+c*(v/B)≤c*c+c-1 := by
  have he := Nat.mod_add_div v B
  have hp : 0<c := by norm_num [c]
  rw [hb] at he ⊢
  simp only [Nat.mul_one] at he ⊢
  norm_num [B,c] at *
  omega

/-- 第二折叠的精细上界。 -/
theorem second_fine_bound (l h : Nat) (hl : l<B) (hh : h<B) :
    (l+c*h)%B+c*((l+c*h)/B)≤B-1+c*c := by
  have hq := first_high_bound l h hl hh
  have hr := Nat.mod_lt (l+c*h) (show 0<B by norm_num [B])
  have hb : 0<B := by norm_num [B]
  norm_num [B,c] at *
  omega

/-- 第三折叠不再溢出，进位为真时甚至已规范化。 -/
theorem third_bound (v : Nat) (hv : v≤B-1+c*c) :
    v%B+c*(v/B)<B := by
  have hc : c*c+c-1<p := by norm_num [c,p,B]
  have hp : p<B := by norm_num [p,B,c]
  have hv2 : v<2*B := by
    have hcc : c*c<B := by norm_num [c,B]
    omega
  have hb := carry_bound v hv2
  by_cases hz : v/B=0
  · simp only [hz,Nat.mul_zero,Nat.add_zero]
    exact Nat.mod_lt v (by norm_num [B])
  · have ho : v/B=1 := Nat.le_antisymm hb (Nat.one_le_iff_ne_zero.mpr hz)
    exact lt_of_le_of_lt (third_carry_bound v hv ho) (hc.trans hp)

/-- 一个字内的值只需试减一次 p。 -/
theorem normalize (w : Nat) (hw : w<B) :
    w-(if p≤w then p else 0)=w%p := by
  have hp : 0<p := by norm_num [p,B,c]
  have hB : B<2*p := by norm_num [p,B,c]
  split_ifs with h
  · have hr : w-p<p := by omega
    rw [Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt hr]
  · simp only [Nat.sub_zero]
    exact (Nat.mod_eq_of_lt (by omega)).symm

/-- 两次后续折叠与规范化的合成结果。 -/
theorem reduced_square_word (l h : Nat) (hl : l<B) (hh : h<B) :
    let u := l+c*h
    let v := u%B+c*(u/B)
    let w := v%B+c*(v/B)
    w-(if p≤w then p else 0)=(l+B*h)%p := by
  dsimp
  rw [normalize _ (third_bound _ (second_fine_bound l h hl hh)),fold_mod,fold_mod,first_mod]

end ECDSAAdd.Arithmetic.SquareReduction
