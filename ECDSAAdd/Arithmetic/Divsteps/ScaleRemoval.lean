import ECDSAAdd.Arithmetic.ControlledUnaryResources
import ECDSAAdd.Math.Divsteps.Reverse
import ECDSAAdd.Math.Divsteps.Endpoint
import ECDSAAdd.Math.ModularHalving
import Mathlib.Tactic

namespace ECDSAAdd.Arithmetic.Divsteps

/-- One exact modular halving controlled by the reverse walk's active bit.
The active bit is supplied by the walk, not by a separate scale counter. -/
def reverseHalf (active : Wire) (U : ModUnaryLayout) (p : Nat) : Program :=
  controlledHalf active U p

theorem reverseHalf_spec (active : Wire) (U : ModUnaryLayout) (n p Z : Nat) (C : Bool)
    (hw : U.Widths n) (hnd : (active :: U.wires).Nodup)
    (hp : p % 2 = 1) (hpn : p < 2^n) (hZ : Z < p) :
    {{ active=C, U.z=Z, U.work=0 }} reverseHalf active U p
    {{ active=C, U.z=(if C then halveMod p Z else Z), U.work=0 }} :=
  controlledHalf_spec active U n p Z C hw hnd hp hpn hZ

theorem reverseHalf_counts (active : Wire) (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) (hn : 0 < n) :
    toffoliCount (reverseHalf active U p) = 3*n+2 ∧
    measurementCount (reverseHalf active U p) = 2*n :=
  ⟨(controlledUnary_counts active U n p hw hn).1,
    (controlledUnary_counts active U n p hw hn).2.1⟩

theorem reverseHalf_wires (active : Wire) (U : ModUnaryLayout) (n p : Nat)
    (hw : U.Widths n) (hn : 0 < n) :
    wires (reverseHalf active U p) = (active :: U.z ++ U.core.work ++ [U.flag]).toFinset :=
  (controlledUnary_wires active U n p hw hn).2

/-- Value update for a sequence of reverse-slot activity bits. Frozen slots
leave the accumulator unchanged. This list is mathematical bookkeeping,
not a register or a quantum count allocated by `reverseHalf`. -/
def halveActive (p : Nat) : List Bool → Nat → Nat
  | [], r => r
  | active :: rest, r => halveActive p rest (if active then halveMod p r else r)

theorem halveActive_eq (p r : Nat) (activity : List Bool) :
    halveActive p activity r = (halveMod p)^[activity.count true] r := by
  induction activity generalizing r with
  | nil => simp [halveActive]
  | cons active rest ih =>
    cases active <;> simp [halveActive, ih, Function.iterate_succ_apply]

theorem halveActive_correct (p r : Nat) (activity : List Bool)
    (hp : p % 2 = 1) (hr : r < p) :
    halveActive p activity r < p ∧
    (halveActive p activity r : ZMod p) * 2^(activity.count true) = r := by
  rw [halveActive_eq]
  exact halve_mod_iterate p (activity.count true) r hp hr

/-- If the scaled endpoint carries 2^t times the desired result and the
reverse walk contains exactly t active steps, its halvings remove the scale.
The actual walk must establish the activity count and endpoint relation. -/
theorem halveActive_remove_scale (p r t : Nat) [Fact p.Prime]
    (activity : List Bool) (target : ZMod p)
    (hp : p % 2 = 1) (hr : r < p) (h2 : (2 : ZMod p) ≠ 0)
    (ht : activity.count true = t) (hscaled : (r : ZMod p) = target * 2^t) :
    (halveActive p activity r : ZMod p) = target := by
  apply mul_right_cancel₀ (pow_ne_zero t h2)
  simpa [ht, hscaled] using (halveActive_correct p r activity hp hr).2

/-- The activity schedule is read in reverse order, including frozen slots. -/
def reverseActivities (p x : Int) (N : Nat) : List Bool :=
  ((List.range N).map fun i => decide ((ECDSAAdd.Divsteps.zWalk p x i).g ≠ 0)).reverse

/-- Freezing implies that exactly the first t forward slots, hence exactly
t reverse slots, are active. There is no approximation of the stopping time. -/
theorem reverseActivities_count (p x : Int) (N t : Nat) (ht : t ≤ N)
    (hstop : (ECDSAAdd.Divsteps.zWalk p x t).g = 0)
    (hbefore : ∀ i < t, (ECDSAAdd.Divsteps.zWalk p x i).g ≠ 0) :
    (reverseActivities p x N).count true = t := by
  have hflags (i : Nat) : decide ((ECDSAAdd.Divsteps.zWalk p x i).g ≠ 0) =
      decide (i < t) := by
    by_cases hi : i < t
    · simp [hi, hbefore i hi]
    · have hti : t ≤ i := by omega
      have he := ECDSAAdd.Divsteps.zWalk_frozen p x t hstop (i-t)
      rw [Nat.add_sub_of_le hti] at he
      simp [hi, he, hstop]
  have hc (n : Nat) : ((List.range n).map fun i => decide (i < t)).count true = min n t := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.count_append, ih]
      by_cases hn : n < t <;> simp [hn] <;> omega
  simp only [reverseActivities, List.count_reverse]
  simp_rw [hflags]
  simpa [min_eq_right ht] using hc N

theorem reverseWalk_remove_scale (p x N t r : Nat) [Fact p.Prime]
    (target : ZMod p) (hp : p % 2 = 1) (hr : r < p) (h2 : (2 : ZMod p) ≠ 0)
    (ht : t ≤ N) (hstop : (ECDSAAdd.Divsteps.zWalk p x t).g = 0)
    (hbefore : ∀ i < t, (ECDSAAdd.Divsteps.zWalk p x i).g ≠ 0)
    (hscaled : (r : ZMod p) = target * 2^t) :
    (halveActive p (reverseActivities p x N) r : ZMod p) = target := by
  apply halveActive_remove_scale p r t (reverseActivities p x N) target hp hr h2
  · exact reverseActivities_count p x N t ht hstop hbefore
  · exact hscaled

end ECDSAAdd.Arithmetic.Divsteps
