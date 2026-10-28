import ECDSAAdd.Math.SkywalkNat

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.SkywalkNat

/-- A terminal logical state is padded by genuine identity transitions. -/
theorem iter_fixed_of_u_zero (z : State) (i : Nat) (hz : z.u=0) :
    step^[i] z=z := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [step,hz,if_true]

/-- Strict value widths lose one unit of total exponent at a nonterminal step.
The small-source odd branch exchanges the two exponent witnesses. No sampled
width, bitLength estimate, or product-only rounding is used. -/
theorem step_exponent_budget (z : State) (a b : Nat)
    (hu0 : 0<z.u) (hv0 : 0<z.v) (hu : z.u<2^a) (hv : z.v<2^b) :
    ∃ a' b', a'+b'+1=a+b ∧ (step z).u<2^a' ∧ (step z).v<2^b' := by
  cases a with
  | zero => simp only [pow_zero] at hu; omega
  | succ a =>
    cases b with
    | zero => simp only [pow_zero] at hv; omega
    | succ b =>
      have ua : z.u<2^a*2 := by simpa only [pow_succ] using hu
      have vb : z.v<2^b*2 := by simpa only [pow_succ] using hv
      have uh : z.u/2<2^a := by omega
      have ud : (z.u-z.v)/2<2^a := by omega
      have vd : (z.v-z.u)/2<2^b := by omega
      have hz : z.u≠0 := by omega
      by_cases he : z.u%2=0
      · refine ⟨a,b+1,by omega,?_,?_⟩
        · simpa only [step,if_neg hz,if_pos he] using uh
        · simpa only [step,if_neg hz,if_pos he] using hv
      · by_cases hle : z.v≤z.u
        · refine ⟨a,b+1,by omega,?_,?_⟩
          · simpa only [step,if_neg hz,if_neg he,if_pos hle] using ud
          · simpa only [step,if_neg hz,if_neg he,if_pos hle] using hv
        · refine ⟨b,a+1,by omega,?_,?_⟩
          · simpa only [step,if_neg hz,if_neg he,if_neg hle] using vd
          · simpa only [step,if_neg hz,if_neg he,if_neg hle] using hu

private theorem budget_aux : ∀ k a b (z : State), a+b=k →
    0<z.v → z.v%2=1 → z.u<2^a → z.v<2^b →
      (step^[k-1] z).u=0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro a b z hab hv0 hvodd hu hv
    by_cases hz : z.u=0
    · rw [iter_fixed_of_u_zero z (k-1) hz]
      exact hz
    · have hu0 : 0<z.u := Nat.pos_of_ne_zero hz
      obtain ⟨a',b',hnext,hu',hv'⟩ := step_exponent_budget z a b hu0 hv0 hu hv
      have lower : a'+b'<k := by omega
      have valid := step_v_odd_pos z hv0 hvodd
      have tail := ih (a'+b') lower a' b' (step z) rfl
        valid.1 valid.2 hu' hv'
      have huExp : 0<a := by
        by_contra h
        have ha : a=0 := by omega
        rw [ha,pow_zero] at hu
        omega
      have hvExp : 0<b := by
        by_contra h
        have hb : b=0 := by omega
        rw [hb,pow_zero] at hv
        omega
      have rounds : k-1=(a'+b'-1)+1 := by omega
      rw [rounds,Function.iterate_succ_apply]
      exact tail

/-- Positive odd v and two strict width witnesses give a+b−1 rounds,
including initially terminal states and every terminal padding suffix. -/
theorem iter_u_zero_budget (z : State) (a b : Nat) (hv0 : 0<z.v)
    (hvodd : z.v%2=1) (hu : z.u<2^a) (hv : z.v<2^b) :
    (step^[a+b-1] z).u=0 :=
  budget_aux (a+b) a b z rfl hv0 hvodd hu hv

attribute [local irreducible] Nat.iterate

/-- Exact all-input termination, one round stronger than the product bound.
The unchanged coprimality/odd-positive hypotheses identify terminal v=1. -/
theorem terminates_2n_sub_one (p x n : Nat) (hp0 : 0<p) (_hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^n) (hx : x<2^n) (hc : x.Coprime p) :
    (step^[2*n-1] (init x p)).u=0 ∧ (step^[2*n-1] (init x p)).v=1 := by
  have hu := iter_u_zero_budget (init x p) n n hp0 hpodd hx hp
  have index : n+n-1=2*n-1 := by omega
  rw [index] at hu
  have valid := iter_valid (2*n-1) (init x p) hp0 hpodd
  have hg : (step^[2*n-1] (init x p)).u.gcd (step^[2*n-1] (init x p)).v=1 :=
    valid.2.2.trans hc
  rw [hu,Nat.gcd_zero_left] at hg
  exact ⟨hu,hg⟩

theorem terminates_canonical_sub_one (p x n : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^n) (hx : x<p) (hc : p.Coprime x) :
    (step^[2*n-1] (init x p)).u=0 ∧ (step^[2*n-1] (init x p)).v=1 :=
  terminates_2n_sub_one p x n hp0 hx0 hpodd hp (hx.trans hp) hc.symm

/-- Complete256-bit canonical range: the state before round512 is terminal. -/
theorem terminates_511 (p x : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^256) (hx : x<p) (hc : x.Coprime p) :
    (step^[511] (init x p)).u=0 ∧ (step^[511] (init x p)).v=1 := by
  simpa only [Nat.reduceMul,Nat.reduceSub] using
    (terminates_2n_sub_one p x 256 hp0 hx0 hpodd hp (hx.trans hp) hc)

/-- Padding beyond the improved horizon changes no logical state. -/
theorem terminal_padding (p x n j : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpodd : p%2=1) (hp : p<2^n) (hx : x<2^n) (hc : x.Coprime p) :
    step^[j] (step^[2*n-1] (init x p))=step^[2*n-1] (init x p) :=
  iter_fixed_of_u_zero _ j (terminates_2n_sub_one p x n hp0 hx0 hpodd hp hx hc).1

end ECDSAAdd.SkywalkNat
#print axioms ECDSAAdd.SkywalkNat.step_exponent_budget
#print axioms ECDSAAdd.SkywalkNat.iter_u_zero_budget
#print axioms ECDSAAdd.SkywalkNat.terminates_2n_sub_one
#print axioms ECDSAAdd.SkywalkNat.terminates_511
#print axioms ECDSAAdd.SkywalkNat.terminal_padding
