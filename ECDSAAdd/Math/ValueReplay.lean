import ECDSAAdd.Math.ValueWalk
import ECDSAAdd.Math.BitcoinPrimes

namespace ECDSAAdd
open Secp256k1

/-- 按记录交换两份域载荷；不根据载荷重新判断分支。 -/
def valueReplaySwap (b : Bool) (v : Fp × Fp) : Fp × Fp :=
  if b then (v.2,v.1) else v

/-- 正回放：交换、条件减、活动时模减半、交换还原。 -/
def valueReplayStep (active : Bool) (code : Bool × Bool) (v : Fp × Fp) : Fp × Fp :=
  let t := valueReplaySwap code.1 v
  let x := t.1 - if code.2 then t.2 else 0
  valueReplaySwap code.1 (if active then x/2 else x,t.2)

/-- 逆回放是独立的前向算术式：模加倍在条件加之前。 -/
def valueReplayUnstep (active : Bool) (code : Bool × Bool) (v : Fp × Fp) : Fp × Fp :=
  let t := valueReplaySwap code.1 v
  let x := (if active then 2*t.1 else t.1) + if code.2 then t.2 else 0
  valueReplaySwap code.1 (x,t.2)

private theorem fp_two_ne_zero : (2 : Fp) ≠ 0 := by
  change (2 : ZMod p) ≠ 0
  decide

theorem valueReplayStep_add (a : Bool) (c : Bool × Bool) (x y : Fp × Fp) :
    valueReplayStep a c (x+y)=valueReplayStep a c x+valueReplayStep a c y := by
  rcases c with ⟨s,t⟩
  cases a <;> cases s <;> cases t <;>
    apply Prod.ext <;> simp [valueReplayStep,valueReplaySwap] <;> ring

theorem valueReplayStep_smul (a : Bool) (c : Bool × Bool) (r : Fp) (x : Fp × Fp) :
    valueReplayStep a c (r • x)=r • valueReplayStep a c x := by
  rcases c with ⟨s,t⟩
  cases a <;> cases s <;> cases t <;>
    apply Prod.ext <;> simp [valueReplayStep,valueReplaySwap] <;> ring

theorem valueReplayUnstep_step (a : Bool) (c : Bool × Bool) (x : Fp × Fp) :
    valueReplayUnstep a c (valueReplayStep a c x)=x := by
  rcases c with ⟨s,t⟩
  cases a <;> cases s <;> cases t <;>
    apply Prod.ext <;> simp [valueReplayStep,valueReplayUnstep,valueReplaySwap] <;>
    field_simp [fp_two_ne_zero] <;> ring

theorem valueReplayStep_unstep (a : Bool) (c : Bool × Bool) (x : Fp × Fp) :
    valueReplayStep a c (valueReplayUnstep a c x)=x := by
  rcases c with ⟨s,t⟩
  cases a <;> cases s <;> cases t <;>
    apply Prod.ext <;> simp [valueReplayStep,valueReplayUnstep,valueReplaySwap] <;>
    field_simp [fp_two_ne_zero]

/-- 所有记录按时间顺序保存；恢复方向使用相反的函数复合次序。 -/
def valueReplay : List (Bool × (Bool × Bool)) → Fp × Fp → Fp × Fp
  | [], x => x
  | c::cs, x => valueReplay cs (valueReplayStep c.1 c.2 x)

def valueReplayInverse : List (Bool × (Bool × Bool)) → Fp × Fp → Fp × Fp
  | [], x => x
  | c::cs, x => valueReplayUnstep c.1 c.2 (valueReplayInverse cs x)

theorem valueReplay_smul (cs : List (Bool × (Bool × Bool))) (r : Fp) (x : Fp × Fp) :
    valueReplay cs (r • x)=r • valueReplay cs x := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih => simp only [valueReplay,valueReplayStep_smul,ih]

theorem valueReplay_add (cs : List (Bool × (Bool × Bool))) (x y : Fp × Fp) :
    valueReplay cs (x+y)=valueReplay cs x+valueReplay cs y := by
  induction cs generalizing x y with
  | nil => rfl
  | cons c cs ih => simp only [valueReplay,valueReplayStep_add,ih]

theorem valueReplayInverse_replay (cs : List (Bool × (Bool × Bool))) (x : Fp × Fp) :
    valueReplayInverse cs (valueReplay cs x)=x := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih => simp only [valueReplay,valueReplayInverse,ih,valueReplayUnstep_step]

theorem valueReplay_replayInverse (cs : List (Bool × (Bool × Bool))) (x : Fp × Fp) :
    valueReplay cs (valueReplayInverse cs x)=x := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih => simp only [valueReplay,valueReplayInverse,valueReplayStep_unstep,ih]

/-- 数值轨迹唯一确定两位记录与活动序列，载荷不参与选择。 -/
def valueTrace : Nat → ValueState → List (Bool × (Bool × Bool))
  | 0, _ => []
  | n+1, z => (decide (z.v ≠ 0),valueCode z)::valueTrace n (valueStep z)

@[simp] theorem valueTrace_length (n : Nat) (z : ValueState) :
    (valueTrace n z).length=n := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [valueTrace,ih]

private theorem cast_half (n : Nat) (he : n%2=0) :
    ((n/2 : Nat) : Fp)=(n : Fp)/2 := by
  apply (eq_div_iff fp_two_ne_zero).2
  norm_cast
  exact congrArg (fun k : Nat => (k : Fp)) (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero he))

/-- 同一记录的域变换与整数值走相符；除法只作用于偶数差。 -/
theorem valueStep_replay (z : ValueState) :
    valueReplayStep (decide (z.v ≠ 0)) (valueCode z) ((z.u : Fp),(z.v : Fp)) =
      (((valueStep z).u : Fp),((valueStep z).v : Fp)) := by
  by_cases hv : z.v=0
  · simp [valueReplayStep,valueReplaySwap,valueCode,valueStep,hv]
  by_cases hu : z.u%2=0
  · simp [valueReplayStep,valueReplaySwap,valueCode,valueStep,hv,hu,cast_half z.u hu]
  by_cases he : z.v%2=0
  · simp [valueReplayStep,valueReplaySwap,valueCode,valueStep,hv,hu,he,cast_half z.v he]
  by_cases hc : z.v<z.u
  · have ht : z.v≤z.u := by omega
    have heven : (z.u-z.v)%2=0 := by omega
    simp [valueReplayStep,valueReplaySwap,valueCode,valueStep,hv,hu,he,hc,
      cast_half _ heven,Nat.cast_sub ht]
  · have ht : z.u≤z.v := by omega
    have heven : (z.v-z.u)%2=0 := by omega
    simp [valueReplayStep,valueReplaySwap,valueCode,valueStep,hv,hu,he,hc,
      cast_half _ heven,Nat.cast_sub ht]

theorem valueReplay_trace (n : Nat) (z : ValueState) :
    valueReplay (valueTrace n z) ((z.u : Fp),(z.v : Fp)) =
      (((valueStep^[n] z).u : Fp),((valueStep^[n] z).v : Fp)) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [valueTrace,valueReplay,valueStep_replay,ih,Function.iterate_succ_apply]

/-- secp256k1 instance of the width envelope: in the secp256k1 value walk, u and v at round j<512 fit in `valueWidth 257 j` bits. -/
theorem dialogWalk_width (x j : Nat) (hx0 : 0<x) (hx : x<p) (hj : j<512) :
    (valueStep^[j] (valueInit p x)).u<2^(valueWidth 257 j) ∧
    (valueStep^[j] (valueInit p x)).v<2^(valueWidth 257 j) := by
  have hp : p<2^256 := by norm_num [p]
  have hc : p.Coprime x := by
    apply Secp256k1.p_prime.coprime_iff_not_dvd.mpr
    intro hd
    exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)
  have hpx : p*x<2^512 := by
    rw [show (512:Nat)=256+256 by norm_num,pow_add]
    exact Nat.mul_lt_mul'' hp (hx.trans hp)
  have hp' : p<2^257 := by rw [show (257:Nat)=256+1 by norm_num,pow_succ]; omega
  exact valueIter_width p x 257 j hc hpx hp' (hx.trans hp') hj

/-- 512轮在域中把(p,X)送到(1,0)，这是商公式的数值证据。 -/
theorem valueReplay_terminal (x : Nat) (hx0 : 0<x) (hx : x<p) :
    valueReplay (valueTrace 512 (valueInit p x)) (0,(x : Fp))=(1,0) := by
  have hp : p<2^256 := by norm_num [p]
  have hc : p.Coprime x := by
    apply Secp256k1.p_prime.coprime_iff_not_dvd.mpr
    intro hd
    exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)
  have ht := valueIter_terminal p x 256 (by norm_num [p]) hx0 hp (hx.trans hp) hc
  have hr := valueReplay_trace 512 (valueInit p x)
  change valueReplay _ ((p : Fp),(x : Fp))=_ at hr
  have hpcast : (p : Fp)=0 := by exact ZMod.natCast_self p
  rw [hpcast] at hr
  exact hr.trans (Prod.ext (congrArg (fun n : Nat => (n : Fp)) ht.2.1)
    (congrArg (fun n : Nat => (n : Fp)) ht.1))

/-- 原地商：同一记录作用于任意载荷，包括零载荷。 -/
theorem dialog_quotient (x : Nat) (y : Fp) (hx0 : 0<x) (hx : x<p) :
    valueReplay (valueTrace 512 (valueInit p x)) (0,y)=(y/(x : Fp),0) := by
  have hnx : (x : Fp) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hx] at hv
    simp only [ZMod.val_zero] at hv
    omega
  have he : ((0 : Fp),y)=(y/(x : Fp)) • (0,(x : Fp)) := by
    apply Prod.ext <;> simp [div_mul_cancel₀ y hnx]
  rw [he,valueReplay_smul,valueReplay_terminal x hx0 hx]
  simp

/-- 逆向回放给原地积；无需另一次域求逆或乘积清理电路。 -/
theorem dialog_product (x : Nat) (y : Fp) (hx0 : 0<x) (hx : x<p) :
    valueReplayInverse (valueTrace 512 (valueInit p x)) (y,0)=(0,y*(x : Fp)) := by
  have hnx : (x : Fp) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hx] at hv
    simp only [ZMod.val_zero] at hv
    omega
  have hq := dialog_quotient x (y*(x : Fp)) hx0 hx
  rw [mul_div_cancel_right₀ y hnx] at hq
  rw [← hq,valueReplayInverse_replay]

end ECDSAAdd
