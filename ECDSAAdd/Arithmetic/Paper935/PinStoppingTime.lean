import ECDSAAdd.Arithmetic.Paper935.PinInvariants

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- The retained offset identifies the first ideal zero, not the fixed walk
length. This is the exponent required for final inverse scaling. -/
theorem pinWalk_stopping_time (tmin : Nat) (positive : 0<tmin) (p x : Int)
    (noEarly : ¬EarlyZero tmin p x) (n : Nat)
    (stopped : (pinWalk tmin p x n).frozen=true) :
    ∃ t,t≤n ∧ t=tmin+(pinWalk tmin p x n).offset ∧
      (∀ u<t,(zWalk p x u).g≠0) ∧ (zWalk p x t).g=0 ∧
      (pinWalk tmin p x n).rows=zWalk p x t := by
  have zero : (zWalk p x n).g=0 := by
    have h := (pinWalk_agrees tmin p x noEarly n).2
    simpa only [stopped,decide_eq_true_eq] using h.symm
  have existsZero : ∃ t,(zWalk p x t).g=0 := ⟨n,zero⟩
  let t := Nat.find existsZero
  have ht : (zWalk p x t).g=0 := Nat.find_spec existsZero
  have hn : t≤n := Nat.find_min' existsZero zero
  have first : ∀ u<t,(zWalk p x u).g≠0 := by
    intro u hu
    exact Nat.find_min existsZero hu
  have lower : tmin<t := by
    by_contra h
    exact ((no_early_zero_iff tmin p x).mp noEarly t (by omega)) ht
  have tp : t-1+1=t := by omega
  have detected := pinWalk_first_zero tmin p x noEarly (t-1) (first (t-1) (by omega))
    (by simpa only [tp] using ht)
  rw [tp] at detected
  have tail := pinWalk_frozen_tail tmin p x t (n-t) detected.1
  have nt : t+(n-t)=n := by omega
  rw [nt] at tail
  refine ⟨t,hn,?_,first,ht,?_⟩
  · rw [tail,detected.2]
    omega
  · rw [tail]
    exact (pinWalk_agrees tmin p x noEarly t).1

end ECDSAAdd.Arithmetic.Paper935
