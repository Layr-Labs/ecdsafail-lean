import ECDSAAdd.Math.Kaliski

namespace ECDSAAdd.SkywalkNat

/-- Logical unsigned Stein state. The second rail remains odd and positive. -/
@[ext] structure State where
  u : Nat
  v : Nat
  deriving DecidableEq

def init (x p : Nat) : State := ⟨x,p⟩

/-- Min-source Stein recurrence. The order split expresses absolute difference
without any signed overflow or truncated arithmetic. -/
def step (z : State) : State :=
  if z.u=0 then z
  else if z.u%2=0 then ⟨z.u/2,z.v⟩
  else if z.v≤z.u then ⟨(z.u-z.v)/2,z.v⟩
  else ⟨(z.v-z.u)/2,z.u⟩

/-- Natural absolute difference; exactly one subtraction term can be nonzero. -/
def absdiff (u v : Nat) : Nat := u-v+(v-u)

theorem step_odd_abs_min (z : State) (ho : z.u%2=1) :
    step z=⟨absdiff z.u z.v/2,min z.u z.v⟩ := by
  have hu : z.u≠0 := by omega
  have he : z.u%2≠0 := by omega
  unfold step absdiff
  rw [if_neg hu,if_neg he]
  split_ifs with hle
  · simp [Nat.sub_eq_zero_of_le hle,Nat.min_eq_right hle]
  · have hle' : z.u≤z.v := by omega
    simp [Nat.sub_eq_zero_of_le hle',Nat.min_eq_left hle']

theorem step_v_odd_pos (z : State) (hv0 : 0<z.v) (hvodd : z.v%2=1) :
    0<(step z).v ∧ (step z).v%2=1 := by
  unfold step
  split_ifs with hz he hle <;> (try dsimp) <;> omega

private theorem gcd_half_of_odd (a b : Nat) (ha : a%2=0) (hb : b%2=1) :
    (a/2).gcd b=a.gcd b := by
  have hh : 2*(a/2)=a := by omega
  have htwo : (2:Nat).Coprime b :=
    Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hb)
  have h := Nat.Coprime.gcd_mul_left_cancel (a/2) htwo
  rw [hh] at h
  exact h.symm

/-- General gcd preservation, without assuming the gcd is one. -/
theorem step_gcd (z : State) (hvodd : z.v%2=1) :
    (step z).u.gcd (step z).v=z.u.gcd z.v := by
  unfold step
  split_ifs with hz he hle
  · rfl
  · exact gcd_half_of_odd z.u z.v he hvodd
  · have hdiff : (z.u-z.v)%2=0 := by omega
    change ((z.u-z.v)/2).gcd z.v=z.u.gcd z.v
    rw [gcd_half_of_odd _ _ hdiff hvodd,Nat.gcd_sub_self_left hle]
  · have huodd : z.u%2=1 := by omega
    have hdiff : (z.v-z.u)%2=0 := by omega
    change ((z.v-z.u)/2).gcd z.u=z.u.gcd z.v
    rw [gcd_half_of_odd _ _ hdiff huodd,
      Nat.gcd_sub_self_left (show z.u≤z.v by omega),Nat.gcd_comm z.v z.u]

theorem step_coprime (z : State) (hvodd : z.v%2=1) (hc : z.u.Coprime z.v) :
    (step z).u.Coprime (step z).v := by
  change (step z).u.gcd (step z).v=1
  rw [step_gcd z hvodd]
  exact hc

/-- The nonnegative product contracts even across the identity terminal suffix. -/
theorem step_product_halves (z : State) :
    2*((step z).u*(step z).v)≤z.u*z.v := by
  unfold step
  split_ifs with hz he hle
  · simp [hz]
  · dsimp
    have hh : 2*(z.u/2)≤z.u := by omega
    nlinarith
  · dsimp
    have hh : 2*((z.u-z.v)/2)≤z.u := by omega
    nlinarith
  · dsimp
    have hh : 2*((z.v-z.u)/2)≤z.v := by omega
    nlinarith

theorem iter_product_bound (i : Nat) (z : State) :
    2^i*((step^[i] z).u*(step^[i] z).v)≤z.u*z.v := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply',pow_succ]
    have hh := Nat.mul_le_mul_left (2^i) (step_product_halves (step^[i] z))
    nlinarith

/-- Validity and gcd propagate through any number of rounds. -/
theorem iter_valid (i : Nat) (z : State) (hv0 : 0<z.v) (hvodd : z.v%2=1) :
    0<(step^[i] z).v ∧ (step^[i] z).v%2=1 ∧
      (step^[i] z).u.gcd (step^[i] z).v=z.u.gcd z.v := by
  induction i with
  | zero => exact ⟨hv0,hvodd,rfl⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have hh := step_v_odd_pos (step^[i] z) ih.1 ih.2.1
    exact ⟨hh.1,hh.2,(step_gcd _ ih.2.1).trans ih.2.2⟩

/-- Universal conservative termination: no sampled 393-round envelope. -/
theorem terminates_2n (p x n : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^n) (hx : x<2^n) (hc : x.Coprime p) :
    (step^[2*n] (init x p)).u=0 ∧ (step^[2*n] (init x p)).v=1 := by
  let z := step^[2*n] (init x p)
  have hi := iter_valid (2*n) (init x p) hp0 hpodd
  have hb := iter_product_bound (2*n) (init x p)
  change 2^(2*n)*(z.u*z.v)≤x*p at hb
  have hxp : x*p<2^(2*n) := by
    rw [two_mul,pow_add]
    calc
      x*p < x*2^n := Nat.mul_lt_mul_of_pos_left hp hx0
      _ < 2^n*2^n := Nat.mul_lt_mul_of_pos_right hx (by positivity)
  have hu : z.u=0 := by
    by_contra h
    have hprod : 1≤z.u*z.v := Nat.mul_pos (Nat.pos_of_ne_zero h) hi.1
    have hm := Nat.mul_le_mul_left (2^(2*n)) hprod
    omega
  have hg : z.u.gcd z.v=1 := hi.2.2.trans hc
  rw [hu,Nat.gcd_zero_left] at hg
  exact ⟨hu,hg⟩

/-- Every scalar input in the complete canonical nonzero range is covered. -/
theorem terminates_canonical (p x n : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^n) (hx : x<p) (hc : p.Coprime x) :
    (step^[2*n] (init x p)).u=0 ∧ (step^[2*n] (init x p)).v=1 :=
  terminates_2n p x n hp0 hx0 hpodd hp (hx.trans hp) hc.symm

/-- A common upper bound for both rails is preserved, even when u increases
because a smaller odd source is selected. -/
theorem step_upper (z : State) (B : Nat) (hu : z.u≤B) (hv : z.v≤B) :
    (step z).u≤B ∧ (step z).v≤B := by
  unfold step
  split_ifs <;> (try dsimp) <;> omega

theorem iter_upper (i : Nat) (z : State) (B : Nat) (hu : z.u≤B) (hv : z.v≤B) :
    (step^[i] z).u≤B ∧ (step^[i] z).v≤B := by
  induction i with
  | zero => exact ⟨hu,hv⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact step_upper _ B ih.1 ih.2

theorem step_sum_nonincrease (z : State) : (step z).u+(step z).v≤z.u+z.v := by
  unfold step
  split_ifs <;> (try dsimp) <;> omega

theorem iter_sum_nonincrease (i : Nat) (z : State) :
    (step^[i] z).u+(step^[i] z).v≤z.u+z.v := by
  induction i with
  | zero => exact le_refl _
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (step_sum_nonincrease _).trans ih

/-- Safe rail envelope derived from the exact product bound and terminal gcd.
It concerns logical integer rails, not empirical incumbent carry windows. -/
theorem iter_width (p x n i : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^n) (hx : x<p) (hc : x.Coprime p)
    (hi : i<2*n) :
    let z := step^[i] (init x p)
    z.u<2^(min n (2*n-i)) ∧ z.v<2^(min n (2*n-i)) := by
  let z := step^[i] (init x p)
  have hvld := iter_valid i (init x p) hp0 hpodd
  have hrange := iter_upper i (init x p) p hx.le (le_refl p)
  have hn : z.u<2^n ∧ z.v<2^n := ⟨hrange.1.trans_lt hp,hrange.2.trans_lt hp⟩
  have hsmall : z.u<2^(2*n-i) ∧ z.v<2^(2*n-i) := by
    by_cases hz : z.u=0
    · have hg : z.u.gcd z.v=1 := hvld.2.2.trans hc
      rw [hz,Nat.gcd_zero_left] at hg
      have he : 2≤2^(2*n-i) := by
        calc
          2 = 2^1 := by norm_num
          _ ≤ 2^(2*n-i) := Nat.pow_le_pow_right (by decide) (by omega)
      exact ⟨by rw [hz]; positivity,by rw [hg]; omega⟩
    · have hu0 : 0<z.u := Nat.pos_of_ne_zero hz
      have hv0 : 0<z.v := hvld.1
      have hb := iter_product_bound i (init x p)
      change 2^i*(z.u*z.v)≤x*p at hb
      have hxp : x*p<2^(2*n) := by
        rw [two_mul,pow_add]
        calc
          x*p < x*2^n := Nat.mul_lt_mul_of_pos_left hp hx0
          _ < 2^n*2^n := Nat.mul_lt_mul_of_pos_right (hx.trans hp) (by positivity)
      have hpow : 2^(2*n)=2^i*2^(2*n-i) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow] at hxp
      have hpbound : z.u*z.v<2^(2*n-i) := by
        by_contra hh
        have hm := Nat.mul_le_mul_left (2^i) (Nat.le_of_not_gt hh)
        omega
      have hlu : z.u≤z.u*z.v := by
        calc
          z.u = z.u*1 := by simp
          _ ≤ z.u*z.v := Nat.mul_le_mul_left z.u (by omega)
      have hlv : z.v≤z.u*z.v := by
        calc
          z.v = 1*z.v := by simp
          _ ≤ z.u*z.v := Nat.mul_le_mul_right z.v (by omega)
      exact ⟨hlu.trans_lt hpbound,hlv.trans_lt hpbound⟩
  change z.u<2^(min n (2*n-i)) ∧ z.v<2^(min n (2*n-i))
  rcases le_total n (2*n-i) with he|he
  · rw [Nat.min_eq_left he]
    exact hn
  · rw [Nat.min_eq_right he]
    exact hsmall

end ECDSAAdd.SkywalkNat
