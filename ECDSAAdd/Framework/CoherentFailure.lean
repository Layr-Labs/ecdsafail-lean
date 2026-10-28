import ECDSAAdd.Framework.FailureBudget
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace ECDSAAdd.FailureBudget

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Projection of an amplitude vector onto the exceptional INPUT labels. -/
def badPart (bad : Finset X) (ψ : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => if x ∈ bad then ψ x else 0)

/-- A state's input law is its squared amplitude, not a census histogram. -/
noncomputable def amplitudeLaw (ψ : EuclideanSpace ℂ X) (hn : ‖ψ‖ = 1) : InputLaw X where
  weight x := ‖ψ x‖ ^ 2
  nonneg x := sq_nonneg _
  total := by rw [← EuclideanSpace.norm_sq_eq, hn]; norm_num

theorem badPart_norm_sq (bad : Finset X) (ψ : EuclideanSpace ℂ X)
    (hn : ‖ψ‖ = 1) :
    ‖badPart bad ψ‖ ^ 2 = (amplitudeLaw ψ hn).mass bad := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [badPart, InputLaw.mass, amplitudeLaw, apply_ite]

/-- Squared-amplitude mass is converted to amplitude by a square root. -/
theorem badPart_norm (bad : Finset X) (ψ : EuclideanSpace ℂ X) (hn : ‖ψ‖ = 1) :
    ‖badPart bad ψ‖ = Real.sqrt ((amplitudeLaw ψ hn).mass bad) := by
  rw [← badPart_norm_sq bad ψ hn, Real.sqrt_sq (norm_nonneg _)]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A conditional quantum bridge, deliberately separate from the Boolean
interpreter. Both maps must represent full coherent evolutions in the SAME
output space (including record/environment registers). Their contraction and
agreement on the good subspace must be proved for the physical circuit.
Neither property follows merely from `RecordedAgreement`. -/
structure CoherentAgreement (bad : Finset X)
    (actual ideal : EuclideanSpace ℂ X →L[ℂ] H) : Prop where
  actual_contracts : ∀ v, ‖actual v‖ ≤ ‖v‖
  ideal_contracts : ∀ v, ‖ideal v‖ ≤ ‖v‖
  good_agreement : ∀ v, actual (v - badPart bad v) = ideal (v - badPart bad v)

/-- No postselection or renormalization: compare the complete output vectors,
including failed branches. This is a vector-norm error, not a diamond bound. -/
theorem CoherentAgreement.error_le (bad : Finset X)
    (actual ideal : EuclideanSpace ℂ X →L[ℂ] H)
    (h : CoherentAgreement bad actual ideal) (ψ : EuclideanSpace ℂ X) :
    ‖actual ψ - ideal ψ‖ ≤ 2 * ‖badPart bad ψ‖ := by
  have he := h.good_agreement ψ
  rw [map_sub, map_sub] at he
  have hd : actual ψ - ideal ψ = actual (badPart bad ψ) - ideal (badPart bad ψ) := by
    have hz := congrArg (fun z => z + actual (badPart bad ψ) - ideal ψ) he
    convert hz using 1 <;> abel_nf
  rw [hd]
  calc
    ‖actual (badPart bad ψ) - ideal (badPart bad ψ)‖ ≤
        ‖actual (badPart bad ψ)‖ + ‖ideal (badPart bad ψ)‖ := norm_sub_le _ _
    _ ≤ ‖badPart bad ψ‖ + ‖badPart bad ψ‖ :=
      add_le_add (h.actual_contracts _) (h.ideal_contracts _)
    _ = 2 * ‖badPart bad ψ‖ := by ring

theorem CoherentAgreement.error_le_of_mass (bad : Finset X)
    (actual ideal : EuclideanSpace ℂ X →L[ℂ] H)
    (h : CoherentAgreement bad actual ideal) (ψ : EuclideanSpace ℂ X)
    (hn : ‖ψ‖ = 1) (ε : ℝ) (hm : (amplitudeLaw ψ hn).mass bad ≤ ε) :
    ‖actual ψ - ideal ψ‖ ≤ 2 * Real.sqrt ε := by
  calc
    _ ≤ 2 * ‖badPart bad ψ‖ := h.error_le bad actual ideal ψ
    _ = 2 * Real.sqrt ((amplitudeLaw ψ hn).mass bad) := by rw [badPart_norm bad ψ hn]
    _ ≤ 2 * Real.sqrt ε := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hm) (by norm_num)

/-- A classical budget applies to an input state only after this distribution
matching (or a separate domination argument) has been proved. -/
theorem CoherentAgreement.error_le_of_law (bad : Finset X)
    (actual ideal : EuclideanSpace ℂ X →L[ℂ] H)
    (h : CoherentAgreement bad actual ideal) (μ : InputLaw X)
    (ψ : EuclideanSpace ℂ X) (hn : ‖ψ‖ = 1)
    (matching : ∀ x, ‖ψ x‖ ^ 2 = μ.weight x)
    (ε : ℝ) (hm : μ.mass bad ≤ ε) :
    ‖actual ψ - ideal ψ‖ ≤ 2 * Real.sqrt ε := by
  apply h.error_le_of_mass bad actual ideal ψ hn ε
  convert hm using 1
  exact Finset.sum_congr rfl (fun x _ => matching x)

/-- Sequential errors add in VECTOR NORM along ideal intermediate states.
No independence or multiplication of success probabilities is assumed. -/
theorem composed_error_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (a₁ i₁ : E →L[ℂ] F) (a₂ i₂ : F →L[ℂ] G)
    (contract : ∀ v, ‖a₂ v‖ ≤ ‖v‖) (ψ : E) (δ₁ δ₂ : ℝ)
    (h₁ : ‖a₁ ψ - i₁ ψ‖ ≤ δ₁) (h₂ : ‖a₂ (i₁ ψ) - i₂ (i₁ ψ)‖ ≤ δ₂) :
    ‖a₂ (a₁ ψ) - i₂ (i₁ ψ)‖ ≤ δ₁ + δ₂ := by
  calc
    _ ≤ ‖a₂ (a₁ ψ) - a₂ (i₁ ψ)‖ + ‖a₂ (i₁ ψ) - i₂ (i₁ ψ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ δ₁ + δ₂ := by
      apply add_le_add _ h₂
      rw [← map_sub]
      exact (contract _).trans h₁

/-- Proposed OVERALL semantic specification for complete coherent maps.
The actual and ideal maps are parameters fixed by circuit semantics and the
mathematical operation, not witnesses chosen to satisfy this structure.
An implementation must additionally prove that these maps realize its code;
this file intentionally supplies no fictitious interpreter-to-channel bridge. -/
structure QuantumBudget (actual ideal : EuclideanSpace ℂ X →L[ℂ] H)
    (μ : InputLaw X) (bad : Finset X) (ε : ℝ) : Prop where
  epsilon_nonneg : 0 ≤ ε
  epsilon_lt_one : ε < 1
  failure_bound : μ.mass bad ≤ ε
  actual_isometry : ∀ v, ‖actual v‖ = ‖v‖
  ideal_isometry : ∀ v, ‖ideal v‖ = ‖v‖
  agreement : CoherentAgreement bad actual ideal

/-- The proposed specification entails a bound on every phase choice with the
specified squared amplitudes; it is not a statement only about a classical mix. -/
theorem QuantumBudget.error_le {actual ideal : EuclideanSpace ℂ X →L[ℂ] H}
    {μ : InputLaw X} {bad : Finset X} {ε : ℝ}
    (h : QuantumBudget actual ideal μ bad ε)
    (ψ : EuclideanSpace ℂ X) (hn : ‖ψ‖ = 1)
    (matching : ∀ x, ‖ψ x‖ ^ 2 = μ.weight x) :
    ‖actual ψ - ideal ψ‖ ≤ 2 * Real.sqrt ε :=
  h.agreement.error_le_of_law bad actual ideal μ ψ hn matching ε h.failure_bound

/-- Exact whole-map correctness embeds in the proposed specification with no
exceptional inputs. Existing code still needs its physical realization proof. -/
theorem quantumBudget_exact (ideal : EuclideanSpace ℂ X →L[ℂ] H)
    (μ : InputLaw X) (hi : ∀ v, ‖ideal v‖ = ‖v‖) :
    QuantumBudget ideal ideal μ ∅ 0 := by
  refine ⟨le_rfl, by norm_num, ?_, hi, hi, ?_⟩
  · simp [InputLaw.mass]
  · exact ⟨fun v => le_of_eq (hi v), fun v => le_of_eq (hi v), fun _ => rfl⟩

end ECDSAAdd.FailureBudget
