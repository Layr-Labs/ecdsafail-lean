import ECDSAAdd.Math.SkywalkNat
import ECDSAAdd.Math.SkywalkRails

namespace ECDSAAdd.SkywalkNat

/-- The product controls the sum on the complete coprime trajectory, including
terminal(0,1). The terminal case cannot be inferred from positivity alone. -/
theorem coprime_sum_le_product_succ (z : State) (hv : 0 < z.v) (hg : z.u.gcd z.v=1) :
    z.u+z.v ≤ z.u*z.v+1 := by
  by_cases hu : z.u=0
  · rw [hu,Nat.gcd_zero_left] at hg
    rw [hu,hg]
  · have hu0 : 0 < z.u := Nat.pos_of_ne_zero hu
    have hp : 1 ≤ (z.u-1)*(z.v-1)+1 := by omega
    have he : z.u*z.v+1=z.u+z.v+(z.u-1)*(z.v-1) := by
      have hu' : z.u=(z.u-1)+1 := by omega
      have hv' : z.v=(z.v-1)+1 := by omega
      nth_rw 1 [hu',hv']
      ring_nf
      omega
    omega

/-- Inclusive sum envelope from the exact product bound. No sampled width
profile or early-termination schedule is used. -/
theorem iter_sum_product_width (p x n i : Nat) (hp0 : 0 < p) (hx0 : 0 < x)
    (hpo : p%2=1) (hp : p < 2^n) (hx : x < p) (hc : x.Coprime p)
    (hi : i ≤ 2*n) :
    let z := step^[i] (init x p)
    z.u+z.v ≤ 2^(2*n-i) := by
  let z := step^[i] (init x p)
  have hvalid := iter_valid i (init x p) hp0 hpo
  have hg : z.u.gcd z.v=1 := hvalid.2.2.trans hc
  have hsum := coprime_sum_le_product_succ z hvalid.1 hg
  have hb := iter_product_bound i (init x p)
  change 2^i*(z.u*z.v) ≤ x*p at hb
  have hxp : x*p < 2^(2*n) := by
    rw [two_mul,pow_add]
    calc
      x*p < x*2^n := Nat.mul_lt_mul_of_pos_left hp hx0
      _ < 2^n*2^n := Nat.mul_lt_mul_of_pos_right (hx.trans hp) (by positivity)
  have he : 2^(2*n)=2^i*2^(2*n-i) := by
    rw [←pow_add]
    congr 1
    omega
  rw [he] at hxp
  have hprod : z.u*z.v < 2^(2*n-i) := by
    by_contra hnot
    have hm := Nat.mul_le_mul_left (2^i) (Nat.le_of_not_gt hnot)
    omega
  change z.u+z.v ≤ 2^(2*n-i)
  omega

/-- Initial common cap from monotone sum, independent of the product cap. -/
theorem iter_sum_initial_width (p x n i : Nat) (hp : p < 2^n) (hx : x < p) :
    let z := step^[i] (init x p)
    z.u+z.v < 2^(n+1) := by
  have hsum := iter_sum_nonincrease i (init x p)
  change (step^[i] (init x p)).u+(step^[i] (init x p)).v ≤ x+p at hsum
  have hx' : x < 2^n := hx.trans hp
  dsimp only
  rw [pow_succ]
  omega

end ECDSAAdd.SkywalkNat

namespace ECDSAAdd.SkywalkRails

private theorem sumwidth_signed_abs (s : Bool) (u : Nat) : |signed s (u:Int)|=(u:Int) := by
  cases s with
  | false => exact Int.abs_natCast u
  | true =>
    change |-(u:Int)|=(u:Int)
    rw [abs_neg]
    exact Int.abs_natCast u

/-- Whole input rails have an inclusive envelope. Equality at the positive
upper endpoint must not be mistaken for a narrower signed decoding theorem. -/
theorem encode_abs_sum_bound (g s : Bool) (u v B : Nat) (hs : u+v ≤ B) :
    |(encode g s (u:Int) (v:Int)).a| ≤ (B:Int) ∧
    |(encode g s (u:Int) (v:Int)).b| ≤ (B:Int) := by
  have hu : (u:Int) ≤ B := by omega
  have hlarge : |(u:Int)+(v:Int)| ≤ (B:Int) := by
    rw [abs_of_nonneg (show 0 ≤ (u:Int)+(v:Int) by omega)]
    omega
  have hsmall : |signed s (u:Int)| ≤ (B:Int) := by
    rw [sumwidth_signed_abs]
    exact hu
  cases g
  · exact ⟨hlarge,hsmall⟩
  · exact ⟨hsmall,hlarge⟩

private theorem even_power (k : Nat) (hk : 0 < k) :
    ((2^k:Nat):Int)=2*((2^(k-1):Nat):Int) := by
  have he : (2^k:Nat)=2^(k-1)*2 := by
    calc
      2^k = 2^((k-1)+1) := by congr 1; omega
      _ = 2^(k-1)*2 := pow_succ 2 (k-1)
  rw [he,Nat.cast_mul]
  ring

/-- An odd rail cannot attain an even power-of-two endpoint. -/
private theorem odd_abs_strict (o : Int) (k : Nat) (hk : 0 < k)
    (ho : o%2=1) (hb : |o| ≤ ((2^k:Nat):Int)) : |o| < ((2^k:Nat):Int) := by
  have he := even_power k hk
  have hm : ((2^k:Nat):Int)%2=0 := by omega
  by_contra hnot
  have hx : |o|=((2^k:Nat):Int) := le_antisymm hb (le_of_not_gt hnot)
  by_cases hz : 0 ≤ o
  · rw [abs_of_nonneg hz] at hx
    omega
  · rw [abs_of_neg (by omega)] at hx
    omega

/-- The routed arithmetic operands admit one fewer sign-padding bit than a
naive sum-of-individual-widths bound: oddO is strictly below2^k, while evenE
is below2^k after halving. Keep the original full sign for the half operation.
This theorem does not change any circuit or the complete512-round schedule. -/
theorem route_half_width (a b : Int) (k : Nat) (hk : 0 < k)
    (hp : (a+b)%2=1) (ha : |a| ≤ ((2^k:Nat):Int)) (hb : |b| ≤ ((2^k:Nat):Int)) :
    |(route a b).2| < ((2^k:Nat):Int) ∧
    |(route a b).1/2| ≤ ((2^(k-1):Nat):Int) := by
  have hroute : |(route a b).1| ≤ ((2^k:Nat):Int) ∧
      |(route a b).2| ≤ ((2^k:Nat):Int) ∧ (route a b).2%2=1 := by
    by_cases he : a%2=0
    · have ho : odd a=false := by simp [odd,he]
      rw [route,ho]
      refine ⟨ha,hb,?_⟩
      change b%2=1
      omega
    · have ho : odd a=true := by simp [odd,he]
      rw [route,ho]
      refine ⟨hb,ha,?_⟩
      change a%2=1
      omega
  refine ⟨odd_abs_strict _ k hk hroute.2.2 hroute.2.1,?_⟩
  have he := even_power k hk
  have hr := abs_le.mp hroute.1
  apply abs_le.mpr
  omega

end ECDSAAdd.SkywalkRails
