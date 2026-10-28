import ECDSAAdd.Math.HornerMultiply
import ECDSAAdd.Math.BitcoinCurve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace ECDSAAdd

/-- secp256k1 的模数低四位为15，故四位Montgomery修正系数就是低四位本身。 -/
theorem secp256k1_mod_sixteen : p % 16 = 15 := by decide

/-- 一轮四位约减，保留低位记录以便正向恢复。 -/
def montgomeryStep (q a x d : Nat) : Nat :=
  let u := a+d*x
  (u+(u%16)*q)/16

/-- 低位为15的奇模数满足精确整除；这里没有舍入误差。 -/
theorem montgomery_divisible (q u : Nat) (hq : q%16=15) :
    u+(u%16)*q = 16*(u/16+(u%16)*(q/16+1)) := by
  have hu := Nat.mod_add_div u 16
  have hp := Nat.mod_add_div q 16
  rw [hq] at hp
  calc
    _ = (u%16+16*(u/16))+(u%16)*(15+16*(q/16)) := by rw [hu,hp]
    _ = _ := by ring

theorem montgomeryStep_exact (q a x d : Nat) (hq : q%16=15) :
    16*montgomeryStep q a x d = a+d*x+((a+d*x)%16)*q := by
  dsimp [montgomeryStep]
  conv_lhs => rw [montgomery_divisible q _ hq]
  simpa using (montgomery_divisible q (a+d*x) hq).symm

/-- 261位承接加数与约减项；本界也覆盖乘数的任意四位窗口。 -/
theorem montgomery_window_bound (q a x d : Nat)
    (ha : a<2*q) (hx : x<q) (hd : d<16) :
    a+d*x+((a+d*x)%16)*q < 32*q := by
  have hm := Nat.mod_lt (a+d*x) (by decide : 0<16)
  have hd' : d≤15 := by omega
  have hm' : (a+d*x)%16≤15 := by omega
  have hdx := Nat.mul_le_mul_right x hd'
  have hmq := Nat.mul_le_mul_right q hm'
  nlinarith

theorem montgomeryStep_bound (q a x d : Nat)
    (ha : a<2*q) (hx : x<q) (hd : d<16) :
    montgomeryStep q a x d < 2*q := by
  have h := montgomery_window_bound q a x d ha hx hd
  dsimp [montgomeryStep]
  omega

/-- 反向窗口先恢复整除前的数，再减修正项；所得低四位恰可清历史。 -/
theorem montgomeryStep_restore (q a x d : Nat) (hq : q%16=15) :
    16*montgomeryStep q a x d - ((a+d*x)%16)*q = a+d*x := by
  rw [montgomeryStep_exact q a x d hq]
  omega

/-- 规范化一次足够；借位保留到反规范化阶段。 -/
theorem montgomery_normalize (q a : Nat) (ha : a<2*q) :
    (if a<q then a else a-q) = a%q := by
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · have hr : a-q<q := by omega
    have he : a=q+(a-q) := by omega
    conv_rhs => rw [he]
    simp [Nat.mod_eq_of_lt hr]

/-- 按低位窗口逐轮处理乘数。 -/
def montgomeryValue (q X Y : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => montgomeryStep q (montgomeryValue q X Y i) X ((Y/16^i)%16)

/-- 各轮修正系数的数学累计值；电路中保存的是逐轮低四位。 -/
def montgomeryQuotient (q X Y : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => montgomeryQuotient q X Y i +
      16^i*((montgomeryValue q X Y i+((Y/16^i)%16)*X)%16)

theorem montgomeryValue_bound (q X Y i : Nat) (hX : X<q) :
    montgomeryValue q X Y i<2*q := by
  induction i with
  | zero => simp only [montgomeryValue]; omega
  | succ i ih =>
    exact montgomeryStep_bound q _ X _ ih hX (Nat.mod_lt _ (by decide))

/-- 精确整数循环不变量，记录项没有被隐去。 -/
theorem montgomeryValue_invariant (q X Y i : Nat) (hq : q%16=15) :
    16^i*montgomeryValue q X Y i = X*(Y%16^i)+q*montgomeryQuotient q X Y i := by
  induction i with
  | zero => simp [montgomeryValue,montgomeryQuotient,Nat.mod_one]
  | succ i ih =>
    have hs := montgomeryStep_exact q (montgomeryValue q X Y i) X ((Y/16^i)%16) hq
    simp only [montgomeryValue,montgomeryQuotient,Nat.pow_succ,Nat.mod_mul]
    calc
      _ = 16^i*(16*montgomeryStep q (montgomeryValue q X Y i) X ((Y/16^i)%16)) := by ring
      _ = _ := by rw [hs]; nlinarith [ih]

/-- 处理完全部窗口后乘数前缀就是整个输入。 -/
theorem montgomeryValue_finish (q X Y k : Nat) (hq : q%16=15) (hY : Y<16^k) :
    16^k*montgomeryValue q X Y k = X*Y+q*montgomeryQuotient q X Y k := by
  simpa [Nat.mod_eq_of_lt hY] using montgomeryValue_invariant q X Y k hq

/-- Montgomery中间值的标准表示转换，不向外部坐标暴露Montgomery表示。 -/
theorem montgomery_standard_conversion {q : Nat} [Fact q.Prime]
    (x y r : ZMod q) (hr : r≠0) :
    ((x*y*r⁻¹)*(r*r))*r⁻¹ = x*y := by
  field_simp [hr]

end ECDSAAdd
