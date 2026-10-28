import ECDSAAdd.Arithmetic.Paper935.FusedSymbolicBudget

namespace ECDSAAdd.Arithmetic.Paper935
open FailureBudget FiniteUnitary RecordedQuantum

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Conditional empirical application, NOT a constructor from sample counts.
The nine mass inequalities in `bounds` are assumptions about the population
law μ. Observations alone do not prove them, including when a count is zero.
The observation counts are exclusive cells on the same original labels. -/
structure EmpiricalBudget (μ : InputLaw X) (events : FailureEvents X)
    (scaling : Finset X) (calls : X → List FusedCall) where
  sampleCount : Nat
  sampleCount_pos : 0 < sampleCount
  observations : Fin 9 → Nat
  observations_total_le : (∑ i, observations i) ≤ sampleCount
  bounds : FusedMassBounds μ events scaling (fusedFailures calls)

/-- A descriptive sample fraction. No population mass inequality follows. -/
noncomputable def EmpiricalBudget.observedRate {μ : InputLaw X} {events : FailureEvents X}
    {scaling : Finset X} {calls : X → List FusedCall}
    (b : EmpiricalBudget μ events scaling calls) (i : Fin 9) : ℝ :=
  (b.observations i : ℝ) / b.sampleCount

/-- Reuses the exact nine-cell identity; even this conditional application
never equates population mass to the observed fraction. -/
theorem empirical_nine_mass (μ : InputLaw X) (events : FailureEvents X)
    (scaling : Finset X) (calls : X → List FusedCall)
    (b : EmpiricalBudget μ events scaling calls) :
    μ.mass (scalingBad events scaling ∪ (fusedFailures calls).bad) =
      (fusedExactBounds μ events scaling (fusedFailures calls)).total ∧
    μ.mass (scalingBad events scaling ∪ (fusedFailures calls).bad) ≤ b.bounds.total :=
  ⟨(fusedExactBounds_total μ events scaling (fusedFailures calls)).symm,b.bounds.mass_le⟩

/-- Numerical good-call obligations only. The physical hmr_pre_of_not_bad
consumer additionally needs its actual register binding, not sample counts. -/
theorem empirical_calls_good (μ : InputLaw X) (events : FailureEvents X)
    (scaling : Finset X) (calls : X → List FusedCall)
    (_b : EmpiricalBudget μ events scaling calls) (x : X)
    (good : x ∉ scalingBad events scaling ∪ (fusedFailures calls).bad) :
    ∀ call ∈ calls x, call.enabled=true →
      call.RowGood ∧ call.LiftGood ∧ call.HornerGood ∧ call.SignGood := by
  apply (fusedFailures_good calls x).mp
  intro hx
  exact good (Finset.mem_union_right _ hx)

omit [DecidableEq X] in
/-- A denominator law is a pushforward of the original label law, not an
independent uniform law. Joint denominators may be encoded together in Y. -/
theorem induced_denominator_mass {Y : Type*} [Fintype Y] [DecidableEq Y]
    (μ : InputLaw X) (denominators : X → Y) (event : Finset Y) :
    (μ.push denominators).mass event =
      μ.mass (Finset.univ.filter (fun x => denominators x ∈ event)) :=
  μ.push_mass denominators event

/-- Conditional 2√ε application. Actual all-tape agreement, population bounds,
normalization, matching input law and total<1 are explicit. No numeric ε. -/
theorem empirical_error {n l : Nat} (c : Circuit n 0 l)
    (ι : X ↪ Bits n) (idealOp : X ≃ X) (μ : InputLaw X)
    (events : FailureEvents X) (scaling : Finset X) (calls : X → List FusedCall)
    (b : EmpiricalBudget μ events scaling calls) (hlt : b.bounds.total < 1)
    (hr : RecordedAgreement c.program (fun x => extend (ι x))
      (fun x => extend (ι (idealOp x)))
      (scalingBad events scaling ∪ (fusedFailures calls).bad))
    (ψ : EuclideanSpace ℂ (Bits n)) (hn : ‖ψ‖=1)
    (matching : ∀x, ‖ψ x‖^2=(μ.push ι).weight x) :
    ‖actual c ψ-ideal l (encodedPerm ι idealOp) ψ‖ ≤ 2*Real.sqrt b.bounds.total :=
  fused_error_of_bounds c ι idealOp μ events scaling calls b.bounds hlt hr ψ hn matching

end ECDSAAdd.Arithmetic.Paper935
