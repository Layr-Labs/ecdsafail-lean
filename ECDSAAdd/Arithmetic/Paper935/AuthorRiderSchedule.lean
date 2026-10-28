import ECDSAAdd.Arithmetic.Paper935.PinStoppingTime
import ECDSAAdd.Arithmetic.Divsteps.ScaleRemoval

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- Author rider activity in reverse order over the armed window only.
The first 498 scale halvings belong to the seam, not to this rider list. -/
def authorRiderActivities (p x : Int) : List Bool :=
  ((List.range 35).map fun i => !(pinWalk 498 p x (498+i)).frozen).reverse

theorem authorRiderActivities_count (p x : Int) (noEarly : ¬EarlyZero 498 p x)
    (stopped : (pinWalk 498 p x 533).frozen=true) :
    (authorRiderActivities p x).count true=(pinWalk 498 p x 533).offset := by
  obtain ⟨t,upper,offset,first,zero,_⟩ :=
    pinWalk_stopping_time 498 (by omega) p x noEarly 533 stopped
  have flags (i : Nat) : (!(pinWalk 498 p x (498+i)).frozen)=decide (i<t-498) := by
    rw [(pinWalk_agrees 498 p x noEarly (498+i)).2]
    by_cases h : 498+i<t
    · have nz := first (498+i) h
      simp [nz,show i<t-498 by omega]
    · have hz := zWalk_frozen p x t zero (498+i-t)
      rw [show t+(498+i-t)=498+i by omega] at hz
      simp [hz,zero,show ¬i<t-498 by omega]
  have counts (n : Nat) : ((List.range n).map fun i => decide (i<t-498)).count true=min n (t-498) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ,List.map_append,List.count_append,ih]
      by_cases h : n<t-498 <;> simp [h] <;> omega
  simp only [authorRiderActivities,List.count_reverse]
  simp_rw [flags]
  rw [counts,min_eq_right (by omega)]
  omega

/-- The seam's 498 unconditional halvings and the armed reverse rider
perform exactly the stored stopping time's number of modular halvings. -/
theorem authorSeamRider_halves (p : Nat) (x : Int) (r : Nat)
    (noEarly : ¬EarlyZero 498 p x) (stopped : (pinWalk 498 p x 533).frozen=true) :
    ECDSAAdd.Arithmetic.Divsteps.halveActive p (authorRiderActivities p x) ((halveMod p)^[498] r)=
      (halveMod p)^[498+(pinWalk 498 p x 533).offset] r := by
  rw [ECDSAAdd.Arithmetic.Divsteps.halveActive_eq,authorRiderActivities_count p x noEarly stopped]
  rw [Nat.add_comm 498,Function.iterate_add_apply]

/-- Canonical modular scale relation for the mathematical seam and rider. -/
theorem authorSeamRider_correct (p : Nat) (x : Int) (r : Nat) (odd : p%2=1) (range : r<p)
    (noEarly : ¬EarlyZero 498 p x) (stopped : (pinWalk 498 p x 533).frozen=true) :
    let out := ECDSAAdd.Arithmetic.Divsteps.halveActive p (authorRiderActivities p x) ((halveMod p)^[498] r)
    out<p ∧ (out : ZMod p)*2^(498+(pinWalk 498 p x 533).offset)=r := by
  dsimp only
  rw [authorSeamRider_halves p x r noEarly stopped]
  exact halve_mod_iterate p _ r odd range

end ECDSAAdd.Arithmetic.Paper935
