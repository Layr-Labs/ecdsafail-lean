import ECDSAAdd.Framework.RecordedHoare
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ECDSAAdd.FailureBudget

/-- A named finite input law. No uniformity or independence is implicit. -/
structure InputLaw (X : Type*) [Fintype X] where
  weight : X → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

variable {X : Type*} [Fintype X]

/-- Probability of an explicitly supplied input event, not of a measurement tape. -/
def InputLaw.mass (μ : InputLaw X) (event : Finset X) : ℝ :=
  ∑ x ∈ event, μ.weight x

theorem InputLaw.mass_nonneg (μ : InputLaw X) (event : Finset X) :
    0 ≤ μ.mass event := Finset.sum_nonneg (fun x _ => μ.nonneg x)

theorem InputLaw.mass_mono (μ : InputLaw X) {a b : Finset X} (h : a ⊆ b) :
    μ.mass a ≤ μ.mass b := Finset.sum_le_sum_of_subset_of_nonneg h (fun x _ _ => μ.nonneg x)

theorem InputLaw.mass_univ (μ : InputLaw X) : μ.mass Finset.univ = 1 := μ.total

theorem InputLaw.mass_le_one (μ : InputLaw X) (a : Finset X) : μ.mass a ≤ 1 := by
  simpa only [μ.mass_univ] using μ.mass_mono (Finset.subset_univ a)

theorem InputLaw.mass_empty (μ : InputLaw X) : μ.mass ∅ = 0 := by simp [mass]

variable [DecidableEq X]

/-- No disjointness or independence hypothesis is needed for the union bound. -/
theorem InputLaw.mass_union_le (μ : InputLaw X) (a b : Finset X) :
    μ.mass (a ∪ b) ≤ μ.mass a + μ.mass b := by
  have h : μ.mass (a ∪ b) + μ.mass (a ∩ b) = μ.mass a + μ.mass b := Finset.sum_union_inter
  have hn := μ.mass_nonneg (a ∩ b)
  unfold mass at *
  linarith

/-- Union-bound accounting over any finite list of stage events on original inputs. -/
theorem InputLaw.mass_events_le (μ : InputLaw X) (events : List (Finset X)) :
    μ.mass (events.foldr (· ∪ ·) ∅) ≤ (events.map μ.mass).sum := by
  induction events with
  | nil => simp [InputLaw.mass]
  | cons a rest ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    exact (μ.mass_union_le _ _).trans (add_le_add le_rfl ih)

/-- A budget is non-vacuous only together with a specified law and an explicit
bound below one; a downstream application must choose its numerical target. -/
structure CertifiedEvent (μ : InputLaw X) where
  event : Finset X
  epsilon : ℝ
  nonneg : 0 ≤ epsilon
  lt_one : epsilon < 1
  bound : μ.mass event ≤ epsilon

omit [DecidableEq X] in
theorem CertifiedEvent.not_univ (μ : InputLaw X) (e : CertifiedEvent μ) :
    e.event ≠ Finset.univ := by
  intro he
  have hb := e.bound
  rw [he, μ.mass_univ] at hb
  exact (not_le_of_gt e.lt_one) hb

/-- Exact all-tape success semantics. Initial and final encodings include all
ancillas and coordinates; equal State includes phase, not just output values.
The caller must identify `bad` from the actual trace, independently of this
predicate. This is not a Born-rule or channel-semantics theorem. -/
def RecordedAgreement (p : RecordedProgram) (input output : X → BasisState)
    (bad : Finset X) : Prop :=
  ∀ x, x ∉ bad → ∀ phase tape,
    runWithTape p tape 0 ⟨phase, input x⟩ = ⟨phase, output x⟩

omit [Fintype X] in
/-- Both stage events are pulled back to the SAME original input labels.
Using two unrelated uniform laws at successive calls would be unsound. -/
theorem RecordedAgreement.seq {p q : RecordedProgram}
    {input middle output : X → BasisState} {a b : Finset X}
    (hp : RecordedAgreement p input middle a)
    (hq : RecordedAgreement q middle output b) :
    RecordedAgreement (recordedThen p q) input output (a ∪ b) := by
  intro x hx phase tape
  have ha : x ∉ a := fun h => hx (Finset.mem_union_left b h)
  have hb : x ∉ b := fun h => hx (Finset.mem_union_right a h)
  rw [recordedThen_run, hp x ha phase tape]
  exact hq x hb phase _

omit [Fintype X] [DecidableEq X] in
/-- Zero exceptional inputs recovers the original pointwise exact obligation. -/
theorem recordedAgreement_empty_iff (p : RecordedProgram) (input output : X → BasisState) :
    RecordedAgreement p input output ∅ ↔
      ∀ x phase tape, runWithTape p tape 0 ⟨phase, input x⟩ = ⟨phase, output x⟩ := by
  simp [RecordedAgreement]

/-- The canonical event from a supplied execution trace and failure predicate.
The implementation must prove the trace describes the actual schedule. -/
def traceEvent {Trace : Type*} (trace : X → Trace) (fails : Trace → Prop)
    [DecidablePred fails] : Finset X := Finset.univ.filter (fun x => fails (trace x))

omit [DecidableEq X] in
theorem mem_traceEvent {Trace : Type*} (trace : X → Trace) (fails : Trace → Prop)
    [DecidablePred fails] (x : X) : x ∈ traceEvent trace fails ↔ fails (trace x) := by
  simp [traceEvent]

/-- Explicit coverage keeps an implementation failure event from being omitted
from a declared budget. Concrete traces and failure reasons are supplied by
an implementation, rather than invented by the generic Framework. -/
def CoversFailure {Trace : Type*} (trace : X → Trace) (fails : Trace → Prop)
    (bad : Finset X) : Prop := ∀ x, fails (trace x) → x ∈ bad

omit [Fintype X] in
theorem coversFailure_union {Trace : Type*} {trace : X → Trace}
    {fails₁ fails₂ : Trace → Prop} {a b : Finset X}
    (h₁ : CoversFailure trace fails₁ a) (h₂ : CoversFailure trace fails₂ b) :
    CoversFailure trace (fun t => fails₁ t ∨ fails₂ t) (a ∪ b) := by
  intro x hx
  rcases hx with hx | hx
  · exact Finset.mem_union_left b (h₁ x hx)
  · exact Finset.mem_union_right a (h₂ x hx)

/-- A finite classical reference register can be included in the input label.
Its marginal is computed, not assumed uniform or independent. -/
def InputLaw.marginal {R : Type*} [Fintype R] (μ : InputLaw (X × R)) : InputLaw X where
  weight x := ∑ r, μ.weight (x, r)
  nonneg x := Finset.sum_nonneg (fun r _ => μ.nonneg (x, r))
  total := by rw [← Fintype.sum_prod_type]; exact μ.total

omit [DecidableEq X] in
theorem InputLaw.mass_product {R : Type*} [Fintype R]
    (μ : InputLaw (X × R)) (bad : Finset X) :
    μ.mass (bad ×ˢ Finset.univ) = μ.marginal.mass bad := by
  simp only [mass, marginal, Finset.sum_product]

end ECDSAAdd.FailureBudget
