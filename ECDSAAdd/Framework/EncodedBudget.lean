import ECDSAAdd.Framework.RecordedPaths
import Mathlib.Logic.Equiv.Fintype

/-! Input laws and measured budgets for explicitly encoded mathematical inputs.
The encoding includes every auxiliary bit. Unencoded bit strings have zero
input mass, but are still included in the exceptional set: no correctness on
dirty auxiliary inputs is silently demanded. The ideal permutation is fixed
by the mathematical operation and encoding, independently of the program. -/

namespace ECDSAAdd.FailureBudget
open FiniteUnitary RecordedQuantum

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Push an explicit input law through a deterministic encoding. -/
noncomputable def InputLaw.push (μ : InputLaw X) (f : X → Y) : InputLaw Y where
  weight y := ∑ x, if f x = y then μ.weight x else 0
  nonneg y := Finset.sum_nonneg (fun x _ => by split_ifs; exact μ.nonneg x; exact le_rfl)
  total := by
    rw [Finset.sum_comm]
    simpa using μ.total

omit [DecidableEq X] in
theorem InputLaw.push_mass (μ : InputLaw X) (f : X → Y) (event : Finset Y) :
    (μ.push f).mass event = μ.mass (Finset.univ.filter (fun x => f x ∈ event)) := by
  simp only [InputLaw.mass, InputLaw.push]
  rw [Finset.sum_comm]
  simp [Finset.sum_filter]

@[simp] theorem InputLaw.push_weight_image (μ : InputLaw X) (ι : X ↪ Y) (x : X) :
    (μ.push ι).weight (ι x) = μ.weight x := by
  simp [InputLaw.push, ι.injective.eq_iff]

omit [DecidableEq X] in
theorem InputLaw.push_weight_outside (μ : InputLaw X) (f : X → Y) (y : Y)
    (hy : y ∉ Set.range f) : (μ.push f).weight y = 0 := by
  have h : ∀ x, f x ≠ y := fun x hx => hy ⟨x, hx⟩
  simp [InputLaw.push, h]

/-- Include all states outside the encoding, even though they have zero mass. -/
def encodedBad (ι : X ↪ Y) (bad : Finset X) : Finset Y :=
  Finset.univ.filter (fun y => ¬ ∃ x, ι x = y ∧ x ∉ bad)

@[simp] theorem mem_encodedBad_image (ι : X ↪ Y) (bad : Finset X) (x : X) :
    ι x ∈ encodedBad ι bad ↔ x ∈ bad := by
  simp [encodedBad, ι.injective.eq_iff]

theorem InputLaw.push_mass_encodedBad (μ : InputLaw X) (ι : X ↪ Y) (bad : Finset X) :
    (μ.push ι).mass (encodedBad ι bad) = μ.mass bad := by
  rw [μ.push_mass]
  congr 1
  ext x
  simp

/-- Extend a mathematical permutation by identity outside the clean encoding. -/
def encodedPerm (ι : X ↪ Y) (e : X ≃ X) : Y ≃ Y := Equiv.Perm.viaFintypeEmbedding e ι

omit [Fintype Y] [DecidableEq X] in
@[simp] theorem encodedPerm_image (ι : X ↪ Y) (e : X ≃ X) (x : X) :
    encodedPerm ι e (ι x) = ι (e x) := Equiv.Perm.viaFintypeEmbedding_apply_image e ι x

/-- Only good, encoded inputs require an all-tape execution proof. -/
theorem recordedAgreement_encoded {n : Nat} (p : RecordedProgram)
    (ι : X ↪ Bits n) (e : X ≃ X) (bad : Finset X)
    (hr : RecordedAgreement p (fun x => extend (ι x)) (fun x => extend (ι (e x))) bad) :
    RecordedAgreement p extend (fun y => extend (encodedPerm ι e y)) (encodedBad ι bad) := by
  intro y hy phase tape
  have h : ∃ x, ι x = y ∧ x ∉ bad := by simpa [encodedBad] using hy
  obtain ⟨x, rfl, hx⟩ := h
  simpa only [encodedPerm_image] using hr x hx phase tape

/-- Application of the physical measured bridge to an encoded input law.
The typed circuit supplies support, legal record references and proper gates;
all-tape correctness and the actual event mass bound remain explicit. -/
theorem budget_of_encoded {n l : Nat} (c : Circuit n 0 l)
    (ι : X ↪ Bits n) (e : X ≃ X) (μ : InputLaw X) (bad : Finset X) (ε : ℝ)
    (he : 0 ≤ ε) (hlt : ε < 1) (hm : μ.mass bad ≤ ε)
    (hr : RecordedAgreement c.program (fun x => extend (ι x))
      (fun x => extend (ι (e x))) bad) :
    QuantumBudget (actual c).toContinuousLinearMap
      (ideal l (encodedPerm ι e)).toContinuousLinearMap
      (μ.push ι) (encodedBad ι bad) ε := by
  apply budget_of_recorded c (encodedPerm ι e) (μ.push ι) (encodedBad ι bad) ε he hlt
  · simpa only [InputLaw.push_mass_encodedBad] using hm
  · exact recordedAgreement_encoded c.program ι e bad hr

/-- No conditioning on success: this compares complete output vectors. -/
theorem error_of_encoded {n l : Nat} (c : Circuit n 0 l)
    (ι : X ↪ Bits n) (e : X ≃ X) (μ : InputLaw X) (bad : Finset X) (ε : ℝ)
    (he : 0 ≤ ε) (hlt : ε < 1) (hm : μ.mass bad ≤ ε)
    (hr : RecordedAgreement c.program (fun x => extend (ι x))
      (fun x => extend (ι (e x))) bad)
    (ψ : EuclideanSpace ℂ (Bits n)) (hn : ‖ψ‖ = 1)
    (matching : ∀ x, ‖ψ x‖ ^ 2 = (μ.push ι).weight x) :
    ‖actual c ψ - ideal l (encodedPerm ι e) ψ‖ ≤ 2 * Real.sqrt ε :=
  (budget_of_encoded c ι e μ bad ε he hlt hm hr).error_le ψ hn matching

end ECDSAAdd.FailureBudget
