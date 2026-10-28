import ECDSAAdd.Arithmetic.Paper935.TrajectoryFailures

namespace ECDSAAdd.Arithmetic.Paper935
open FailureBudget
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- An ordered partition of the existing union, not additional failure modes. -/
def FailureEvents.exclusive (e : FailureEvents X) : FailureEvents X :=
  ⟨e.counter,e.history\e.counter,e.deadline\(e.counter∪e.history),
    e.window\((e.counter∪e.history)∪e.deadline)⟩

omit [Fintype X] in
theorem FailureEvents.exclusive_bad (e : FailureEvents X) : e.exclusive.bad=e.bad := by
  ext x
  simp only [FailureEvents.mem_bad,exclusive,Finset.mem_sdiff,Finset.mem_union]
  tauto

private theorem mass_union_difference (μ : InputLaw X) (a b : Finset X) :
    μ.mass (a∪b)=μ.mass a+μ.mass (b\a) := by
  have he : a∪b=a∪(b\a) := by ext x; simp
  have hd : Disjoint a (b\a) := Finset.disjoint_left.mpr (fun _ ha hb => (Finset.mem_sdiff.mp hb).2 ha)
  rw [he,InputLaw.mass,Finset.sum_union hd]
  rfl

/-- Exact mass with overlapping causes counted once. The usual four bounds
remain valid upper bounds, but are not asserted to be the exact total. -/
theorem FailureEvents.mass_exclusive (e : FailureEvents X) (μ : InputLaw X) :
    μ.mass e.bad = ((μ.mass e.exclusive.counter+μ.mass e.exclusive.history)+
      μ.mass e.exclusive.deadline)+μ.mass e.exclusive.window := by
  simp only [FailureEvents.bad,mass_union_difference,exclusive]

/-- Reuse the adopted budget interface with the actual induced events. No
uniform denominator law or independence of times/categories is assumed. -/
noncomputable def trajectoryBounds (input : X → Int) (p : Int)
    (tmin depth steps width : Nat) (capacity : Nat → Nat) (exits : List RowWindow)
    (μ : InputLaw X) : FailureBounds μ (trajectoryEvents input p tmin depth steps width capacity exits).exclusive :=
  let e := (trajectoryEvents input p tmin depth steps width capacity exits).exclusive
  ⟨μ.mass e.counter,μ.mass e.history,μ.mass e.deadline,μ.mass e.window,
    le_rfl,le_rfl,le_rfl,le_rfl⟩

/-- The exact symbolic budget can be sent directly to `budget_of_failureBounds`
once its non-vacuous numerical bound and actual-circuit agreement are proved. -/
theorem trajectoryBounds_total (input : X → Int) (p : Int)
    (tmin depth steps width : Nat) (capacity : Nat → Nat) (exits : List RowWindow)
    (μ : InputLaw X) :
    (trajectoryBounds input p tmin depth steps width capacity exits μ).total =
      μ.mass (trajectoryEvents input p tmin depth steps width capacity exits).bad := by
  exact ((trajectoryEvents input p tmin depth steps width capacity exits).mass_exclusive μ).symm

end ECDSAAdd.Arithmetic.Paper935
