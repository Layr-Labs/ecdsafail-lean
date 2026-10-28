import ECDSAAdd.Framework.FiniteUnitary

/-! Coherent X-basis measurement with a retained record.

The measured bit is exchanged for its outcome coordinate by a Hadamard map.
The data target is represented by the Cleared subtype, so its zero reset is
explicit. Conditional corrections are diagonal signs obtained from correct.
The output is a purification: reading the record gives the outcome law.
This file does not yet induct over arbitrary RecordedProgram streams.
-/

namespace ECDSAAdd.RecordedMeasurement

variable {X : Type*} [Fintype X]

noncomputable def hadamardLinear :
    EuclideanSpace ℂ (Bool × X) →ₗ[ℂ] EuclideanSpace ℂ (Bool × X) where
  toFun ψ := WithLp.toLp 2 (fun bx =>
    (if bx.1 then ψ (false,bx.2) - ψ (true,bx.2)
      else ψ (false,bx.2) + ψ (true,bx.2)) / (Real.sqrt 2 : ℂ))
  map_add' ψ φ := by
    ext ⟨b,x⟩
    cases b <;> simp [add_div] <;> ring
  map_smul' c ψ := by
    ext ⟨b,x⟩
    cases b <;> simp <;> ring

theorem hadamard_norm (ψ : EuclideanSpace ℂ (Bool × X)) :
    ‖hadamardLinear ψ‖ = ‖ψ‖ := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs : ‖hadamardLinear ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    have hp := parallelogram_law_with_norm ℂ (ψ (false,x)) (ψ (true,x))
    simp only [hadamardLinear, LinearMap.coe_mk, AddHom.coe_mk,
      Bool.false_eq_true, ↓reduceIte, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hn, div_pow, h2]
    nlinarith
  nlinarith [norm_nonneg (hadamardLinear ψ), norm_nonneg ψ]

noncomputable def hadamard :
    EuclideanSpace ℂ (Bool × X) →ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × X) where
  toLinearMap := hadamardLinear
  norm_map' := hadamard_norm

def sign (b : Bool) : ℂ := if b then -1 else 1

@[simp] theorem sign_norm (b : Bool) : ‖sign b‖ = 1 := by
  cases b <;> simp [sign]

theorem sign_xor (a b : Bool) : sign (a ^^ b) = sign a * sign b := by
  cases a <;> cases b <;> norm_num [sign]

noncomputable def phaseLinear {Y : Type*} [Fintype Y] (f : Y → Bool) :
    EuclideanSpace ℂ Y →ₗ[ℂ] EuclideanSpace ℂ Y where
  toFun ψ := WithLp.toLp 2 (fun y => sign (f y) * ψ y)
  map_add' ψ φ := by ext y; simp [mul_add]
  map_smul' c ψ := by ext y; simp; ring

theorem phase_norm {Y : Type*} [Fintype Y] (f : Y → Bool)
    (ψ : EuclideanSpace ℂ Y) : ‖phaseLinear f ψ‖ = ‖ψ‖ := by
  have hs : ‖phaseLinear f ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro y _
    simp [phaseLinear]
  nlinarith [norm_nonneg (phaseLinear f ψ), norm_nonneg ψ]

noncomputable def phaseIsometry {Y : Type*} [Fintype Y] (f : Y → Bool) :
    EuclideanSpace ℂ Y →ₗᵢ[ℂ] EuclideanSpace ℂ Y where
  toLinearMap := phaseLinear f
  norm_map' := phase_norm f

open FiniteUnitary

def Cleared (n : Nat) (t : Fin n) := {x : Bits n // x t = false}

instance (n : Nat) (t : Fin n) : Fintype (Cleared n t) := inferInstanceAs (Fintype {x : Bits n // x t = false})
instance (n : Nat) (t : Fin n) : DecidableEq (Cleared n t) := inferInstanceAs (DecidableEq {x : Bits n // x t = false})

def clear {n : Nat} (t : Fin n) (x : Bits n) : Cleared n t :=
  ⟨Function.update x t false, by simp⟩

def splitBit (n : Nat) (t : Fin n) : Bits n ≃ Bool × Cleared n t where
  toFun x := (x t, clear t x)
  invFun bx := Function.update bx.2.val t bx.1
  left_inv x := by
    funext w
    by_cases h : w = t <;> simp [clear, Function.update, h]
  right_inv bx := by
    rcases bx with ⟨b,⟨x,hx⟩⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      funext w
      by_cases h : w = t <;> simp [clear, Function.update, h, hx]

noncomputable def splitIsometry (n : Nat) (t : Fin n) :
    EuclideanSpace ℂ (Bits n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Cleared n t) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitBit n t)

/-- The correction phase is computed by the existing interpreter on reset data.
The Boolean coordinate is the retained measurement outcome, not a discarded branch. -/
def correctionPhase (n : Nat) (t : Fin n) (c₀ c₁ : List Correction)
    (mx : Bool × Cleared n t) : Bool :=
  (correct (if mx.1 then c₁ else c₀) ⟨false,extend mx.2.val⟩).phase

noncomputable def measure (n : Nat) (t : Fin n) (c₀ c₁ : List Correction) :
    EuclideanSpace ℂ (Bits n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Cleared n t) :=
  (phaseIsometry (correctionPhase n t c₀ c₁)).comp
    (hadamard.comp (splitIsometry n t).toLinearIsometry)

theorem measure_norm (n : Nat) (t : Fin n) (c₀ c₁ : List Correction)
    (ψ : EuclideanSpace ℂ (Bits n)) : ‖measure n t c₀ c₁ ψ‖ = ‖ψ‖ :=
  (measure n t c₀ c₁).norm_map ψ

theorem extend_clear (n : Nat) (t : Fin n) (x : Bits n) :
    extend (clear t x).val = writeBit (extend x) t.val false := by
  funext w
  by_cases h : w < n
  · simp [extend, clear, writeBit, Function.update, h, Fin.ext_iff]
  · have ht : w ≠ t.val := by intro he; subst w; exact h t.isLt
    simp [extend, writeBit, Function.update, h, ht]

theorem correct_phase (cs : List Correction) (b : BasisState) (ph : Bool) :
    (correct cs ⟨ph,b⟩).phase = (ph ^^ (correct cs ⟨false,b⟩).phase) := by
  induction cs generalizing ph with
  | nil => simp [correct]
  | cons c cs ih =>
    cases c <;> simp only [correct]
    all_goals rw [ih, ih]
    all_goals simp
    all_goals simpa using (ih _).symm

theorem measurement_basis (n : Nat) (t : Fin n) (c₀ c₁ : List Correction)
    (x : Bits n) (m : Bool) :
    (measureAndCorrect t.val c₀ c₁ m ⟨false,extend x⟩).basis =
      extend (clear t x).val := by
  simp [measureAndCorrect, extend_clear]

theorem measurement_phase (n : Nat) (t : Fin n) (c₀ c₁ : List Correction)
    (x : Bits n) (m : Bool) :
    (measureAndCorrect t.val c₀ c₁ m ⟨false,extend x⟩).phase =
      ((m && x t) ^^ correctionPhase n t c₀ c₁ (m,clear t x)) := by
  simp only [measureAndCorrect, Bool.false_xor]
  rw [correct_phase]
  simp [correctionPhase, extend_clear, extend]

theorem hadamard_single [DecidableEq X] (b m : Bool) (x z : X) :
    hadamard (EuclideanSpace.single (b,x) 1) (m,z) =
      if z = x then sign (m && b) / (Real.sqrt 2 : ℂ) else 0 := by
  cases b <;> cases m <;> by_cases hz : z = x
  all_goals simp [hadamard, hadamardLinear, EuclideanSpace.single_apply, sign, hz]

theorem measure_single (n : Nat) (t : Fin n) (c₀ c₁ : List Correction)
    (x : Bits n) (m : Bool) (z : Cleared n t) :
    measure n t c₀ c₁ (EuclideanSpace.single x 1) (m,z) =
      if z = clear t x then
        sign ((measureAndCorrect t.val c₀ c₁ m ⟨false,extend x⟩).phase) /
          (Real.sqrt 2 : ℂ)
      else 0 := by
  change sign (correctionPhase n t c₀ c₁ (m,z)) *
    (hadamard (splitIsometry n t (EuclideanSpace.single x 1))) (m,z) = _
  rw [show splitIsometry n t (EuclideanSpace.single x 1) =
      EuclideanSpace.single (x t,clear t x) 1 from
    EuclideanSpace.piLpCongrLeft_single (splitBit n t) x 1]
  rw [hadamard_single]
  by_cases hz : z = clear t x
  · subst z
    simp only [↓reduceIte, measurement_phase, sign_xor]
    ring
  · simp [hz]

/-- The outcome distribution is a marginal of the complete output amplitudes.
Interference is included before taking the squared norm. -/
noncomputable def outcomeMass (n : Nat) (t : Fin n) (c₀ c₁ : List Correction)
    (ψ : EuclideanSpace ℂ (Bits n)) (m : Bool) : ℝ :=
  ∑ z, ‖measure n t c₀ c₁ ψ (m,z)‖ ^ 2

theorem outcomeMass_nonneg (n : Nat) (t : Fin n) (c₀ c₁ : List Correction)
    (ψ : EuclideanSpace ℂ (Bits n)) (m : Bool) :
    0 ≤ outcomeMass n t c₀ c₁ ψ m :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem outcomeMass_total (n : Nat) (t : Fin n) (c₀ c₁ : List Correction)
    (ψ : EuclideanSpace ℂ (Bits n)) :
    outcomeMass n t c₀ c₁ ψ false + outcomeMass n t c₀ c₁ ψ true = ‖ψ‖ ^ 2 := by
  rw [← measure_norm n t c₀ c₁ ψ, EuclideanSpace.norm_sq_eq]
  simp [outcomeMass, Fintype.sum_prod_type, add_comm]

theorem measure_apply (n : Nat) (t : Fin n) (c₀ c₁ : List Correction)
    (ψ : EuclideanSpace ℂ (Bits n)) (m : Bool) (z : Cleared n t) :
    measure n t c₀ c₁ ψ (m,z) =
      sign (correctionPhase n t c₀ c₁ (m,z)) *
        ((if m then ψ (Function.update z.val t false) - ψ (Function.update z.val t true)
          else ψ (Function.update z.val t false) + ψ (Function.update z.val t true)) /
          (Real.sqrt 2 : ℂ)) := rfl

theorem hadamard_twice (ψ : EuclideanSpace ℂ (Bool × X)) :
    hadamard (hadamard ψ) = ψ := by
  have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro hz
    rw [hz] at h2
    norm_num at h2
  ext ⟨b,x⟩
  cases b <;> simp only [hadamard, hadamardLinear, LinearIsometry.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Bool.false_eq_true, ↓reduceIte]
  all_goals field_simp
  all_goals ring_nf
  all_goals rw [h2]

/-- Fresh-outcome correction and later use of that same saved outcome have
the same map when no intervening data operation is inserted. -/
theorem measure_correction_comp (n : Nat) (t : Fin n) (c₀ c₁ : List Correction)
    (ψ : EuclideanSpace ℂ (Bits n)) :
    measure n t c₀ c₁ ψ =
      phaseIsometry (correctionPhase n t c₀ c₁) (measure n t [] [] ψ) := by
  ext ⟨m,z⟩
  simp [measure_apply, phaseIsometry, phaseLinear, correctionPhase, correct, sign]

/-- Retaining the outcome also supports any subsequent isometry, including
operations on a larger state space that keeps earlier records. -/
theorem followed_by_norm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (n : Nat) (t : Fin n) (c₀ c₁ : List Correction)
    (next : EuclideanSpace ℂ (Bool × Cleared n t) →ₗᵢ[ℂ] H)
    (ψ : EuclideanSpace ℂ (Bits n)) :
    ‖next (measure n t c₀ c₁ ψ)‖ = ‖ψ‖ := by
  rw [next.norm_map, measure_norm]

theorem measure_bare (n : Nat) (t : Fin n) (ψ : EuclideanSpace ℂ (Bits n)) :
    measure n t [] [] ψ = hadamard (splitIsometry n t ψ) := by
  ext ⟨m,z⟩
  simp [measure, phaseIsometry, phaseLinear, correctionPhase, correct, sign]

/-- An X-plus input has deterministic outcome false. This rules out
treating measurement tapes as uniform random bits on arbitrary inputs. -/
theorem plus_input_output (n : Nat) (t : Fin n) (z : Cleared n t) :
    measure n t [] []
      ((splitIsometry n t).symm (hadamard (EuclideanSpace.single (false,z) 1))) =
        EuclideanSpace.single (false,z) 1 := by
  rw [measure_bare, LinearIsometryEquiv.apply_symm_apply, hadamard_twice]

theorem plus_input_norm (n : Nat) (t : Fin n) (z : Cleared n t) :
    ‖(splitIsometry n t).symm (hadamard (EuclideanSpace.single (false,z) 1))‖ = 1 := by
  rw [(splitIsometry n t).symm.norm_map, hadamard.norm_map]
  simp

theorem plus_input_probability (n : Nat) (t : Fin n) (z : Cleared n t) :
    outcomeMass n t [] []
      ((splitIsometry n t).symm (hadamard (EuclideanSpace.single (false,z) 1))) false = 1 ∧
    outcomeMass n t [] []
      ((splitIsometry n t).symm (hadamard (EuclideanSpace.single (false,z) 1))) true = 0 := by
  simp [outcomeMass, plus_input_output, EuclideanSpace.single_apply, apply_ite]

theorem measurement_phase_general (t : Wire) (c₀ c₁ : List Correction)
    (b : BasisState) (ph m : Bool) :
    (measureAndCorrect t c₀ c₁ m ⟨ph,b⟩).phase =
      (ph ^^ (measureAndCorrect t c₀ c₁ m ⟨false,b⟩).phase) := by
  unfold measureAndCorrect
  rw [correct_phase _ _ (ph ^^ (m && b t))]
  rw [correct_phase _ _ (false ^^ (m && b t))]
  simp only [Bool.false_xor]
  exact Bool.xor_assoc _ _ _

theorem measure_signed_single (n : Nat) (t : Fin n) (c₀ c₁ : List Correction)
    (x : Bits n) (ph m : Bool) (z : Cleared n t) :
    measure n t c₀ c₁ (sign ph • EuclideanSpace.single x 1) (m,z) =
      if z = clear t x then
        sign ((measureAndCorrect t.val c₀ c₁ m ⟨ph,extend x⟩).phase) /
          (Real.sqrt 2 : ℂ)
      else 0 := by
  rw [map_smul]
  change sign ph * measure n t c₀ c₁ (EuclideanSpace.single x 1) (m,z) = _
  rw [measure_single, measurement_phase_general t.val c₀ c₁ (extend x) ph m, sign_xor]
  by_cases hz : z = clear t x <;> simp [hz, mul_div_assoc]

/-- A delayed correction reads a previously stored outcome and preserves
both the data basis and all record labels. The bounded ordinal excludes
future or missing records. -/
def savedPhase (n k : Nat) (j : Fin k) (cs : List Correction)
    (xr : Bits n × (Fin k → Bool)) : Bool :=
  if xr.2 j then (correct cs ⟨false,extend xr.1⟩).phase else false

noncomputable def savedCorrection (n k : Nat) (j : Fin k) (cs : List Correction) :
    EuclideanSpace ℂ (Bits n × (Fin k → Bool)) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits n × (Fin k → Bool)) :=
  phaseIsometry (savedPhase n k j cs)

theorem savedCorrection_norm (n k : Nat) (j : Fin k) (cs : List Correction)
    (ψ : EuclideanSpace ℂ (Bits n × (Fin k → Bool))) :
    ‖savedCorrection n k j cs ψ‖ = ‖ψ‖ :=
  (savedCorrection n k j cs).norm_map ψ

theorem savedPhase_run (n k : Nat) (j : Fin k) (cs : List Correction)
    (x : Bits n) (r : Fin k → Bool) (cursor : Nat) :
    savedPhase n k j cs (x,r) =
      (runWithTape [.phaseFromRecord j.val cs] (List.ofFn r) cursor
        ⟨false,extend x⟩).phase := by
  cases h : r j <;> simp [savedPhase, runWithTape, h]

theorem savedCorrection_single (n k : Nat) (j : Fin k) (cs : List Correction)
    (x : Bits n) (r : Fin k → Bool) (cursor : Nat) :
    savedCorrection n k j cs (EuclideanSpace.single (x,r) 1) =
      sign ((runWithTape [.phaseFromRecord j.val cs] (List.ofFn r) cursor
        ⟨false,extend x⟩).phase) • EuclideanSpace.single (x,r) 1 := by
  rw [← savedPhase_run]
  ext yr
  by_cases h : yr = (x,r)
  · subst yr
    simp [savedCorrection, phaseIsometry, phaseLinear, EuclideanSpace.single_apply]
  · simp [savedCorrection, phaseIsometry, phaseLinear, EuclideanSpace.single_apply, h]

end ECDSAAdd.RecordedMeasurement
