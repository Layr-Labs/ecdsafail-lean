import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring

namespace ECDSAAdd

/-- Kaliski 第一阶段的自然数状态；k 只计入尚未终止的轮。 -/
structure KState where
  u : Nat
  v : Nat
  r : Nat
  s : Nat
  k : Nat

def kaliskiInit (p a : Nat) : KState := ⟨p, a, 0, 1, 0⟩

/-- v=0 后恒等；终止轮本身仍更新系数并增加 k。 -/
def kaliskiStep (z : KState) : KState :=
  if z.v = 0 then z
  else if z.u % 2 = 0 then ⟨z.u/2, z.v, z.r, 2*z.s, z.k+1⟩
  else if z.v % 2 = 0 then ⟨z.u, z.v/2, 2*z.r, z.s, z.k+1⟩
  else if z.v < z.u then ⟨(z.u-z.v)/2, z.v, z.r+z.s, 2*z.s, z.k+1⟩
  else ⟨z.u, (z.v-z.u)/2, 2*z.r, z.r+z.s, z.k+1⟩

/-- 整数等式控制系数大小；两条模等式给出缩放后的逆元。 -/
def KInvariant (p a : Nat) (z : KState) : Prop :=
  0 < z.u ∧ 0 < z.s ∧ z.u*z.s + z.v*z.r = p ∧ z.u.Coprime z.v ∧
  (a : ZMod p)*z.r = -(z.u : ZMod p)*2^z.k ∧
  (a : ZMod p)*z.s = (z.v : ZMod p)*2^z.k

theorem kaliski_init_invariant (p a : Nat) (hp : 0 < p) (ha : p.Coprime a) :
    KInvariant p a (kaliskiInit p a) := by
  simpa [KInvariant, kaliskiInit, hp] using ha

private theorem half_eq (u : Nat) (h : u % 2 = 0) : 2*(u/2) = u := by omega

private theorem half_coprime_left (u v : Nat) (he : u % 2 = 0) (h : u.Coprime v) :
    (u/2).Coprime v :=
  h.of_dvd_left (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero he))

/-- 四种更新都保持整数、互素及缩放逆元不变量。 -/
theorem kaliski_invariant (p a : Nat) (z : KState) (h : KInvariant p a z) :
    KInvariant p a (kaliskiStep z) := by
  obtain ⟨hu, hs, he, hg, hr, ht⟩ := h
  unfold kaliskiStep
  split_ifs with hv hu2 hv2 hlt
  · exact ⟨hu, hs, he, hg, hr, ht⟩
  · have hh := half_eq z.u hu2
    have hh' : (2 : ZMod p)*(z.u/2 : Nat) = z.u := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add] using congrArg (fun n : Nat => (n : ZMod p)) hh
    refine ⟨by dsimp; omega, by dsimp; omega, ?_, half_coprime_left _ _ hu2 hg, ?_, ?_⟩
    · dsimp; nlinarith
    · dsimp; rw [pow_succ, hr]; linear_combination (2 : ZMod p)^z.k * hh'
    · dsimp; push_cast; rw [pow_succ]; linear_combination 2 * ht
  · have hh := half_eq z.v hv2
    have hh' : (2 : ZMod p)*(z.v/2 : Nat) = z.v := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add] using congrArg (fun n : Nat => (n : ZMod p)) hh
    refine ⟨hu, hs, ?_, (half_coprime_left _ _ hv2 hg.symm).symm, ?_, ?_⟩
    · dsimp; nlinarith
    · dsimp; push_cast; rw [pow_succ]; linear_combination 2 * hr
    · dsimp; rw [pow_succ, ht]; linear_combination -(2 : ZMod p)^z.k * hh'
  · have hd : (z.u-z.v)%2 = 0 := by omega
    have hh : 2*((z.u-z.v)/2) + z.v = z.u := by omega
    have hh' : (2 : ZMod p)*((z.u-z.v)/2 : Nat) + z.v = z.u := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add] using congrArg (fun n : Nat => (n : ZMod p)) hh
    refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_, ?_, ?_⟩
    · dsimp; nlinarith
    · exact half_coprime_left _ _ hd ((Nat.coprime_sub_self_left (by omega)).mpr hg)
    · dsimp; push_cast; rw [mul_add, hr, ht, pow_succ]
      linear_combination (2 : ZMod p)^z.k * hh'
    · dsimp; push_cast; rw [pow_succ]; linear_combination 2 * ht
  · have hd : (z.v-z.u)%2 = 0 := by omega
    have hh : 2*((z.v-z.u)/2) + z.u = z.v := by omega
    have hh' : (2 : ZMod p)*((z.v-z.u)/2 : Nat) + z.u = z.v := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add] using congrArg (fun n : Nat => (n : ZMod p)) hh
    refine ⟨hu, by dsimp; omega, ?_, ?_, ?_, ?_⟩
    · dsimp; nlinarith
    · exact (half_coprime_left _ _ hd ((Nat.coprime_sub_self_right (by omega)).mpr hg).symm).symm
    · dsimp; push_cast; rw [pow_succ]; linear_combination 2 * hr
    · dsimp; push_cast; rw [mul_add, hr, ht, pow_succ]
      linear_combination -(2 : ZMod p)^z.k * hh'

/-- 包括终止后的恒等轮：乘积为零时不等式仍成立。 -/
theorem kaliski_product_halves (z : KState) :
    2*((kaliskiStep z).u*(kaliskiStep z).v) ≤ z.u*z.v := by
  unfold kaliskiStep
  split_ifs with hv hu2 hv2 hlt
  · simp [hv]
  · dsimp
    have h : 2*(z.u/2) ≤ z.u := by omega
    nlinarith
  · dsimp
    have h : 2*(z.v/2) ≤ z.v := by omega
    nlinarith
  · dsimp
    have h : 2*((z.u-z.v)/2) ≤ z.u := by omega
    nlinarith
  · dsimp
    have h : 2*((z.v-z.u)/2) ≤ z.v := by omega
    nlinarith

theorem kaliski_iterate_invariant (p a t : Nat) (z : KState) (h : KInvariant p a z) :
    KInvariant p a (kaliskiStep^[t] z) := by
  induction t with
  | zero => exact h
  | succ t ih => rw [Function.iterate_succ_apply']; exact kaliski_invariant p a _ ih

theorem kaliski_product_bound (t : Nat) (z : KState) :
    2^t * ((kaliskiStep^[t] z).u*(kaliskiStep^[t] z).v) ≤ z.u*z.v := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    have h := Nat.mul_le_mul_left (2^t) (kaliski_product_halves (kaliskiStep^[t] z))
    nlinarith

/-- 计数器包括终止轮，恒等填充不再增加。 -/
theorem kaliski_count_bound (t : Nat) (z : KState) : (kaliskiStep^[t] z).k ≤ z.k+t := by
  have one (z : KState) : (kaliskiStep z).k ≤ z.k+1 := by
    unfold kaliskiStep
    split_ifs <;> (try dsimp) <;> omega
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have h := one (kaliskiStep^[t] z)
    omega

/-- 初始 p、a 都小于 2^n 时，固定 2n 轮后 v=0 且 u=1。 -/
theorem kaliski_terminates (p a n : Nat) (hp0 : 0 < p) (ha0 : 0 < a)
    (hp : p < 2^n) (ha : a < 2^n) (hcop : p.Coprime a) :
    (kaliskiStep^[2*n] (kaliskiInit p a)).v = 0 ∧
    (kaliskiStep^[2*n] (kaliskiInit p a)).u = 1 ∧
    (kaliskiStep^[2*n] (kaliskiInit p a)).k ≤ 2*n := by
  let z := kaliskiStep^[2*n] (kaliskiInit p a)
  have hi : KInvariant p a z := kaliski_iterate_invariant p a (2*n) _ (kaliski_init_invariant p a hp0 hcop)
  have hb := kaliski_product_bound (2*n) (kaliskiInit p a)
  change 2^(2*n)*(z.u*z.v) ≤ p*a at hb
  have hpow : 2^(2*n) = 2^n*2^n := by rw [two_mul, pow_add]
  have hpa : p*a < 2^(2*n) := by
    rw [hpow]
    calc p*a < 2^n*a := Nat.mul_lt_mul_of_pos_right hp ha0
      _ ≤ 2^n*2^n := Nat.mul_le_mul_left _ (Nat.le_of_lt ha)
  have hv : z.v = 0 := by
    have hu := hi.1
    by_contra hv
    have hh : 1 ≤ z.u*z.v := Nat.mul_pos hu (Nat.pos_of_ne_zero hv)
    nlinarith
  have hg := hi.2.2.2.1
  rw [Nat.Coprime, hv, Nat.gcd_zero_right] at hg
  exact ⟨hv, hg, by simpa only [kaliskiInit, Nat.zero_add] using kaliski_count_bound (2*n) (kaliskiInit p a)⟩

/-- 活动轮的 r<p；终止轮允许把 r 加倍到接近 2p。 -/
private theorem kaliski_coefficient_bounds (p a t : Nat) (hp0 : 0 < p) (hcop : p.Coprime a) :
    let z := kaliskiStep^[t] (kaliskiInit p a)
    z.s ≤ p ∧ z.r < 2*p := by
  have s_bound (z : KState) (h : KInvariant p a z) : z.s ≤ p := by
    obtain ⟨hu, _, he, _⟩ := h
    nlinarith
  have active_r (z : KState) (h : KInvariant p a z) (hv : z.v ≠ 0) : z.r < p := by
    obtain ⟨hu, hs, he, _⟩ := h
    have hv' := Nat.pos_of_ne_zero hv
    nlinarith
  dsimp
  induction t with
  | zero => simp [kaliskiInit]; omega
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    let z := kaliskiStep^[t] (kaliskiInit p a)
    have hi : KInvariant p a z := kaliski_iterate_invariant p a t _ (kaliski_init_invariant p a hp0 hcop)
    refine ⟨s_bound _ (kaliski_invariant p a z hi), ?_⟩
    change (kaliskiStep z).r < 2*p
    unfold kaliskiStep
    split_ifs with hv hu2 hv2 hlt
    · exact ih.2
    all_goals have hr := active_r z hi hv
    all_goals have hs := s_bound z hi
    all_goals dsimp; omega

/-- 给后续寄存器布局使用的统一范围：r 需要容纳小于 2p 的值。 -/
theorem kaliski_register_bounds (p a t : Nat) (hp0 : 0<p) (hcop : p.Coprime a) :
    let z := kaliskiStep^[t] (kaliskiInit p a)
    z.u ≤ p ∧ z.v ≤ a ∧ z.r < 2*p ∧ z.s ≤ p ∧ z.k ≤ t := by
  let z := kaliskiStep^[t] (kaliskiInit p a)
  have hi : KInvariant p a z := kaliski_iterate_invariant p a t _ (kaliski_init_invariant p a hp0 hcop)
  have hb := kaliski_coefficient_bounds p a t hp0 hcop
  have hv (j : Nat) : (kaliskiStep^[j] (kaliskiInit p a)).v ≤ a := by
    have one (z : KState) : (kaliskiStep z).v ≤ z.v := by
      unfold kaliskiStep
      split_ifs <;> (try dsimp) <;> omega
    induction j with
    | zero => exact le_refl _
    | succ j ih => rw [Function.iterate_succ_apply']; exact (one _).trans ih
  refine ⟨?_, hv t, hb.2, hb.1, ?_⟩
  · have hs := hi.2.1
    have he := hi.2.2.1
    nlinarith
  · simpa only [kaliskiInit, Nat.zero_add] using kaliski_count_bound t (kaliskiInit p a)

end ECDSAAdd
