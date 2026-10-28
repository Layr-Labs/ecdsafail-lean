import ECDSAAdd.Arithmetic.Paper935.FusedFailureEvents
import ECDSAAdd.Framework.EncodedBudget

namespace ECDSAAdd.Arithmetic.Paper935
open FailureBudget FiniteUnitary RecordedQuantum

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Nine bounds on disjoint cells of the SAME original input law. No input
independence, denominator uniformity, or numerical estimate is assumed. -/
structure FusedMassBounds (μ : InputLaw X) (e : FailureEvents X)
    (scaling : Finset X) (f : FusedFailures X) where
  counter : ℝ
  history : ℝ
  deadline : ℝ
  window : ℝ
  scale : ℝ
  row : ℝ
  lift : ℝ
  horner : ℝ
  sign : ℝ
  counter_le : μ.mass e.exclusive.counter ≤ counter
  history_le : μ.mass e.exclusive.history ≤ history
  deadline_le : μ.mass e.exclusive.deadline ≤ deadline
  window_le : μ.mass e.exclusive.window ≤ window
  scale_le : μ.mass (scalingExclusive e scaling) ≤ scale
  row_le : μ.mass (f.exclusiveAfter (scalingBad e scaling)).row ≤ row
  lift_le : μ.mass (f.exclusiveAfter (scalingBad e scaling)).lift ≤ lift
  horner_le : μ.mass (f.exclusiveAfter (scalingBad e scaling)).horner ≤ horner
  sign_le : μ.mass (f.exclusiveAfter (scalingBad e scaling)).sign ≤ sign

def FusedMassBounds.total {μ : InputLaw X} {e : FailureEvents X}
    {scaling : Finset X} {f : FusedFailures X} (b : FusedMassBounds μ e scaling f) : ℝ :=
  b.counter+b.history+b.deadline+b.window+b.scale+b.row+b.lift+b.horner+b.sign

theorem FusedMassBounds.mass_le {μ : InputLaw X} {e : FailureEvents X}
    {scaling : Finset X} {f : FusedFailures X} (b : FusedMassBounds μ e scaling f) :
    μ.mass (scalingBad e scaling∪f.bad) ≤ b.total := by
  rw [fused_nine_mass]
  unfold total
  linarith [b.counter_le,b.history_le,b.deadline_le,b.window_le,b.scale_le,
    b.row_le,b.lift_le,b.horner_le,b.sign_le]

theorem FusedMassBounds.total_nonneg {μ : InputLaw X} {e : FailureEvents X}
    {scaling : Finset X} {f : FusedFailures X} (b : FusedMassBounds μ e scaling f) :
    0 ≤ b.total := le_trans (μ.mass_nonneg _) b.mass_le

/-- Exact cell masses give a symbolic bound without ANY numerical estimates. -/
noncomputable def fusedExactBounds (μ : InputLaw X) (e : FailureEvents X)
    (scaling : Finset X) (f : FusedFailures X) : FusedMassBounds μ e scaling f :=
  ⟨_,_,_,_,_,_,_,_,_,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩

theorem fusedExactBounds_total (μ : InputLaw X) (e : FailureEvents X)
    (scaling : Finset X) (f : FusedFailures X) :
    (fusedExactBounds μ e scaling f).total = μ.mass (scalingBad e scaling∪f.bad) := by
  rw [fused_nine_mass]
  simp only [FusedMassBounds.total,fusedExactBounds]
  ring

/-- Typed circuit legality and all-tape correctness remain explicit. The ideal
operation is supplied independently of the implementation. -/
theorem fused_budget_of_bounds {n l : Nat} (c : Circuit n 0 l)
    (ι : X ↪ Bits n) (idealOp : X ≃ X) (μ : InputLaw X)
    (events : FailureEvents X) (scaling : Finset X) (calls : X → List FusedCall)
    (b : FusedMassBounds μ events scaling (fusedFailures calls)) (hlt : b.total < 1)
    (hr : RecordedAgreement c.program (fun x => extend (ι x))
      (fun x => extend (ι (idealOp x))) (scalingBad events scaling∪(fusedFailures calls).bad)) :
    QuantumBudget (actual c).toContinuousLinearMap
      (ideal l (encodedPerm ι idealOp)).toContinuousLinearMap
      (μ.push ι) (encodedBad ι (scalingBad events scaling∪(fusedFailures calls).bad)) b.total :=
  budget_of_encoded c ι idealOp μ _ b.total b.total_nonneg hlt b.mass_le hr

theorem fused_error_of_bounds {n l : Nat} (c : Circuit n 0 l)
    (ι : X ↪ Bits n) (idealOp : X ≃ X) (μ : InputLaw X)
    (events : FailureEvents X) (scaling : Finset X) (calls : X → List FusedCall)
    (b : FusedMassBounds μ events scaling (fusedFailures calls)) (hlt : b.total < 1)
    (hr : RecordedAgreement c.program (fun x => extend (ι x))
      (fun x => extend (ι (idealOp x))) (scalingBad events scaling∪(fusedFailures calls).bad))
    (ψ : EuclideanSpace ℂ (Bits n)) (hn : ‖ψ‖=1)
    (matching : ∀x, ‖ψ x‖^2=(μ.push ι).weight x) :
    ‖actual c ψ-ideal l (encodedPerm ι idealOp) ψ‖ ≤ 2*Real.sqrt b.total :=
  (fused_budget_of_bounds c ι idealOp μ events scaling calls b hlt hr).error_le ψ hn matching

/-- Exact symbolic nine-cell error bound: no per-cell numerical hypotheses. -/
theorem fused_error_exact {n l : Nat} (c : Circuit n 0 l)
    (ι : X ↪ Bits n) (idealOp : X ≃ X) (μ : InputLaw X)
    (events : FailureEvents X) (scaling : Finset X) (calls : X → List FusedCall)
    (hlt : (fusedExactBounds μ events scaling (fusedFailures calls)).total < 1)
    (hr : RecordedAgreement c.program (fun x => extend (ι x))
      (fun x => extend (ι (idealOp x))) (scalingBad events scaling∪(fusedFailures calls).bad))
    (ψ : EuclideanSpace ℂ (Bits n)) (hn : ‖ψ‖=1)
    (matching : ∀x, ‖ψ x‖^2=(μ.push ι).weight x) :
    ‖actual c ψ-ideal l (encodedPerm ι idealOp) ψ‖ ≤
      2*Real.sqrt (fusedExactBounds μ events scaling (fusedFailures calls)).total :=
  fused_error_of_bounds c ι idealOp μ events scaling calls
    (fusedExactBounds μ events scaling (fusedFailures calls)) hlt hr ψ hn matching

end ECDSAAdd.Arithmetic.Paper935
