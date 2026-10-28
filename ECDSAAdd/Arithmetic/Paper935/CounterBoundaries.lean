import ECDSAAdd.Arithmetic.Paper935.TrajectoryMass
import ECDSAAdd.Math.BitcoinCurve

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

/-- Distribution-free counter range; freezing can only retain an earlier value. -/
theorem pinWalk_counter_bounds (tmin : Nat) (p x : Int) (t : Nat) :
    -(t:Int)≤(pinWalk tmin p x t).rows.z ∧ (pinWalk tmin p x t).rows.z≤(t:Int) := by
  induction t with
  | zero => simp [pinWalk,zSeed]
  | succ t ih =>
    simp only [pinWalk,pinStep]
    split
    · constructor <;> omega
    · simp only [zStep]
      split <;> split <;> dsimp <;> constructor <;> omega

/-- Eleven total signed sites suffice for this coarse full-input bound; this
is NOT the actual seven-site layout or a proposed 935-site allocation. -/
theorem no_counter_failure_eleven (p x : Int) : ¬CounterFailure 498 533 11 p x := by
  rintro ⟨t,ht,hbad⟩
  have bounds := pinWalk_counter_bounds 498 p x t
  apply hbad
  norm_num [PayloadFits]
  constructor <;> omega

/-- A canonical nonzero input, not the excluded zero input. -/
def counterWitness : Int := 2^64

theorem counterWitness_canonical :
    0<counterWitness ∧ counterWitness<(ECDSAAdd.p:Int) := by
  norm_num [counterWitness,ECDSAAdd.p]

theorem counterWitness_at64 :
    (pinWalk 498 (ECDSAAdd.p:Int) counterWitness 64).rows.z=64 := by
  decide +kernel

theorem counterWitness_failure : CounterFailure 498 533 7 (ECDSAAdd.p:Int) counterWitness := by
  refine ⟨64,by decide,?_⟩
  rw [counterWitness_at64]
  norm_num [PayloadFits]

theorem counterWitness_at25_f :
    (pinWalk 498 (ECDSAAdd.p:Int) counterWitness 25).rows.f=(ECDSAAdd.p:Int) := by
  decide +kernel

theorem counterWitness_window_failure : WindowFailure 498 authorWindows (ECDSAAdd.p:Int) counterWitness := by
  apply Or.inr
  refine ⟨24,⟨255,254,25,24⟩,by decide,?_⟩
  intro fit
  have hf := fit.1
  rw [counterWitness_at25_f] at hf
  norm_num [PayloadFits,ECDSAAdd.p] at hf

attribute [local instance] Classical.propDecidable

/-- If an actual input law gives this canonical input positive weight, each
of these events has at least that weight. The two bounds are NOT added. -/
theorem counterWitness_mass_lower {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (μ : InputLaw X) (x : X) (hx : input x=counterWitness) :
    μ.weight x ≤ μ.mass (traceEvent input (CounterFailure 498 533 7 (ECDSAAdd.p:Int))) ∧
    μ.weight x ≤ μ.mass (traceEvent input (WindowFailure 498 authorWindows (ECDSAAdd.p:Int))) := by
  have counter : x∈traceEvent input (CounterFailure 498 533 7 (ECDSAAdd.p:Int)) := by
    rw [mem_traceEvent,hx]
    exact counterWitness_failure
  have window : x∈traceEvent input (WindowFailure 498 authorWindows (ECDSAAdd.p:Int)) := by
    rw [mem_traceEvent,hx]
    exact counterWitness_window_failure
  constructor
  · simpa only [InputLaw.mass,Finset.sum_singleton] using
      μ.mass_mono (Finset.singleton_subset_iff.mpr counter)
  · simpa only [InputLaw.mass,Finset.sum_singleton] using
      μ.mass_mono (Finset.singleton_subset_iff.mpr window)

/-- The existing exclusive partition assigns this witness to counter first;
its window failure is not charged again in any of the later categories. -/
theorem counterWitness_exclusive {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (capacity : Nat → Nat) (x : X) (hx : input x=counterWitness) :
    let e := trajectoryEvents input (ECDSAAdd.p:Int) 498 7 533 7 capacity authorWindows
    x∈e.exclusive.counter ∧ x∉e.exclusive.history ∧ x∉e.exclusive.deadline ∧ x∉e.exclusive.window := by
  dsimp only
  have hc : x∈(trajectoryEvents input (ECDSAAdd.p:Int) 498 7 533 7 capacity authorWindows).counter := by
    simp only [trajectoryEvents,mem_traceEvent,hx]
    exact counterWitness_failure
  simp [FailureEvents.exclusive,hc]

/-- A law supported on this nonzero input has failure mass one. This is a
counterexample to a distribution-free small bound, not the law of point addition. -/
theorem counterWitness_constant_mass {X : Type*} [Fintype X] [DecidableEq X]
    (μ : InputLaw X) :
    μ.mass (traceEvent (fun _ : X => counterWitness) (CounterFailure 498 533 7 (ECDSAAdd.p:Int)))=1 ∧
    μ.mass (traceEvent (fun _ : X => counterWitness) (WindowFailure 498 authorWindows (ECDSAAdd.p:Int)))=1 := by
  have counter : traceEvent (fun _ : X => counterWitness)
      (CounterFailure 498 533 7 (ECDSAAdd.p:Int))=Finset.univ := by
    ext x
    simp only [mem_traceEvent,Finset.mem_univ,iff_true]
    exact counterWitness_failure
  have window : traceEvent (fun _ : X => counterWitness)
      (WindowFailure 498 authorWindows (ECDSAAdd.p:Int))=Finset.univ := by
    ext x
    simp only [mem_traceEvent,Finset.mem_univ,iff_true]
    exact counterWitness_window_failure
  rw [counter,window,μ.mass_univ]
  exact ⟨rfl,rfl⟩

end ECDSAAdd.Arithmetic.Paper935
