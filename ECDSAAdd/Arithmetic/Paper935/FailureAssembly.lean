import ECDSAAdd.Framework.EncodedBudget
import ECDSAAdd.Math.BitcoinPrimes

/-! Preparatory application contracts, not a verified compact inverse circuit.
Events are supplied on ORIGINAL mathematical input labels from the actual
trace. Each event must include every occurrence of its failure mode, across
all stages/calls; no independence, uniformity, or numerical bound is assumed.
The caller still proves all-tape correctness outside their union. -/

namespace ECDSAAdd.Arithmetic.Paper935
open FailureBudget FiniteUnitary RecordedQuantum

local instance : NeZero p := ⟨Secp256k1.p_prime.ne_zero⟩

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Four bookkeeping categories; these sets must come from the execution trace.
`deadline` includes failure to freeze/terminate within the prescribed rounds.
`window` includes every integer/coefficient width violation. -/
structure FailureEvents (X : Type*) where
  counter : Finset X
  history : Finset X
  deadline : Finset X
  window : Finset X

def FailureEvents.bad (events : FailureEvents X) : Finset X :=
  ((events.counter ∪ events.history) ∪ events.deadline) ∪ events.window

omit [Fintype X] in
@[simp] theorem FailureEvents.mem_bad (events : FailureEvents X) (x : X) :
    x ∈ events.bad ↔ x ∈ events.counter ∨ x ∈ events.history ∨
      x ∈ events.deadline ∨ x ∈ events.window := by
  simp [FailureEvents.bad]

/-- Per-category bounds under one common original-input law. -/
structure FailureBounds (μ : InputLaw X) (events : FailureEvents X) where
  counter : ℝ
  history : ℝ
  deadline : ℝ
  window : ℝ
  counter_bound : μ.mass events.counter ≤ counter
  history_bound : μ.mass events.history ≤ history
  deadline_bound : μ.mass events.deadline ≤ deadline
  window_bound : μ.mass events.window ≤ window

def FailureBounds.total {μ : InputLaw X} {events : FailureEvents X}
    (bounds : FailureBounds μ events) : ℝ :=
  ((bounds.counter + bounds.history) + bounds.deadline) + bounds.window

theorem FailureBounds.mass_le {μ : InputLaw X} {events : FailureEvents X}
    (bounds : FailureBounds μ events) : μ.mass events.bad ≤ bounds.total := by
  have h := μ.mass_events_le [events.counter, events.history, events.deadline, events.window]
  simp only [List.foldr_cons, List.foldr_nil, Finset.union_empty,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  have hb := add_le_add (add_le_add (add_le_add bounds.counter_bound bounds.history_bound)
    bounds.deadline_bound) bounds.window_bound
  simpa only [FailureEvents.bad, FailureBounds.total, Finset.union_assoc, add_assoc] using h.trans
    (by simpa only [add_assoc] using hb)

theorem FailureBounds.total_nonneg {μ : InputLaw X} {events : FailureEvents X}
    (bounds : FailureBounds μ events) : 0 ≤ bounds.total :=
  (μ.mass_nonneg events.bad).trans bounds.mass_le

/-- The last classical obligations imply the adopted measured quantum budget.
An extra failure mode cannot simply be omitted: `hr` covers EVERY input outside
these four sets, including zero denominators and all boundary cases. -/
theorem budget_of_failureBounds {n l : Nat} (c : Circuit n 0 l)
    (ι : X ↪ Bits n) (e : X ≃ X) (μ : InputLaw X) (events : FailureEvents X)
    (bounds : FailureBounds μ events) (hlt : bounds.total < 1)
    (hr : RecordedAgreement c.program (fun x => extend (ι x))
      (fun x => extend (ι (e x))) events.bad) :
    QuantumBudget (actual c).toContinuousLinearMap
      (ideal l (encodedPerm ι e)).toContinuousLinearMap
      (μ.push ι) (encodedBad ι events.bad) bounds.total :=
  budget_of_encoded c ι e μ events.bad bounds.total bounds.total_nonneg hlt bounds.mass_le hr

/-- The sum of classical event bounds yields the full-vector quantum error,
for every phase choice with the explicitly encoded input law. -/
theorem error_of_failureBounds {n l : Nat} (c : Circuit n 0 l)
    (ι : X ↪ Bits n) (e : X ≃ X) (μ : InputLaw X) (events : FailureEvents X)
    (bounds : FailureBounds μ events) (hlt : bounds.total < 1)
    (hr : RecordedAgreement c.program (fun x => extend (ι x))
      (fun x => extend (ι (e x))) events.bad)
    (ψ : EuclideanSpace ℂ (Bits n)) (hn : ‖ψ‖ = 1)
    (matching : ∀ x, ‖ψ x‖ ^ 2 = (μ.push ι).weight x) :
    ‖actual c ψ - ideal l (encodedPerm ι e) ψ‖ ≤ 2 * Real.sqrt bounds.total :=
  (budget_of_failureBounds c ι e μ events bounds hlt hr).error_le ψ hn matching

/-- Independent total mathematical inverse; zero maps to zero. This is not a
claim that a future divsteps circuit handles zero without a separate proof. -/
noncomputable def inversePerm : Fp ≃ Fp where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv := inv_inv
  right_inv := inv_inv

@[simp] theorem inversePerm_apply (x : Fp) : inversePerm x = x⁻¹ := rfl

/-- Control, denominator and numerator; all physical ancillas belong to the
separate injective encoding, not to a fictitious uniform ancilla law. -/
abbrev DivisionInput := Bool × Fp × Fp

/-- Total controlled division: disabled or zero-denominator labels are fixed.
On the ordinary arithmetic domain, y is replaced by y/x and x is preserved. -/
noncomputable def divisionPerm : DivisionInput ≃ DivisionInput where
  toFun v := (v.1, v.2.1, if v.1 = true ∧ v.2.1 ≠ 0 then v.2.2 / v.2.1 else v.2.2)
  invFun v := (v.1, v.2.1, if v.1 = true ∧ v.2.1 ≠ 0 then v.2.2 * v.2.1 else v.2.2)
  left_inv v := by
    rcases v with ⟨b,x,y⟩
    by_cases h : b = true ∧ x ≠ 0
    · simp [h, div_mul_cancel₀ y h.2]
    · simp [h]
  right_inv v := by
    rcases v with ⟨b,x,y⟩
    by_cases h : b = true ∧ x ≠ 0
    · simp [h, mul_div_cancel_right₀ y h.2]
    · simp [h]

@[simp] theorem divisionPerm_active (x y : Fp) (hx : x ≠ 0) :
    divisionPerm (true,x,y) = (true,x,y/x) := by simp [divisionPerm, hx]

@[simp] theorem divisionPerm_disabled (x y : Fp) :
    divisionPerm (false,x,y) = (false,x,y) := by simp [divisionPerm]

@[simp] theorem divisionPerm_zero (b : Bool) (y : Fp) :
    divisionPerm (b,0,y) = (b,0,y) := by simp [divisionPerm]

/-- Ready-to-instantiate compact-inverse contract. Input law remains explicit;
no uniform distribution over denominators is inferred from point addition. -/
theorem inverse_budget {n l : Nat} (c : Circuit n 0 l)
    (ι : Fp ↪ Bits n) (μ : InputLaw Fp) (events : FailureEvents Fp)
    (bounds : FailureBounds μ events) (hlt : bounds.total < 1)
    (hr : RecordedAgreement c.program (fun x => extend (ι x))
      (fun x => extend (ι x⁻¹)) events.bad) :
    QuantumBudget (actual c).toContinuousLinearMap
      (ideal l (encodedPerm ι inversePerm)).toContinuousLinearMap
      (μ.push ι) (encodedBad ι events.bad) bounds.total :=
  budget_of_failureBounds c ι inversePerm μ events bounds hlt hr

/-- Point-arithmetic division contract, preserving control and denominator.
This does not assert correctness of the surrounding controlled point addition. -/
theorem division_budget {n l : Nat} (c : Circuit n 0 l)
    (ι : DivisionInput ↪ Bits n) (μ : InputLaw DivisionInput)
    (events : FailureEvents DivisionInput) (bounds : FailureBounds μ events)
    (hlt : bounds.total < 1)
    (hr : RecordedAgreement c.program (fun x => extend (ι x))
      (fun x => extend (ι (divisionPerm x))) events.bad) :
    QuantumBudget (actual c).toContinuousLinearMap
      (ideal l (encodedPerm ι divisionPerm)).toContinuousLinearMap
      (μ.push ι) (encodedBad ι events.bad) bounds.total :=
  budget_of_failureBounds c ι divisionPerm μ events bounds hlt hr

end ECDSAAdd.Arithmetic.Paper935
