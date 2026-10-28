import ECDSAAdd.Framework.GateInverse
import ECDSAAdd.Framework.CoherentFailure

/-! Finite, exact quantum semantics for proper X/CX/CCX programs.

Every wire must lie below n. The basis permutation is derived from run, with
its inverse proved using the reversed gate stream. Its linear extension is
a complex linear isometric equivalence, not an arbitrary realization witness.
No measurements, corrections, tape probabilities, or record environments
are interpreted here. Those require a separate semantics.
-/

namespace ECDSAAdd.FiniteUnitary

abbrev Bits (n : Nat) := Fin n → Bool

/-- Embed the finite register into the interpreter, with zero outside it. -/
def extend {n : Nat} (x : Bits n) : BasisState :=
  fun w => if h : w < n then x ⟨w,h⟩ else false

def restrict (n : Nat) (x : BasisState) : Bits n := fun w => x w.val

@[simp] theorem restrict_extend {n : Nat} (x : Bits n) :
    restrict n (extend x) = x := by
  funext w
  simp [restrict, extend]

theorem run_phase (p : Program) (hp : ProperProgram p) (s : State) (m : List Bool) :
    (run p m s).phase = s.phase := by
  induction p generalizing s with
  | nil => rfl
  | cons i p ih =>
    have hi := hp i (by simp)
    have ht : ProperProgram p := fun j hj => hp j (by simp [hj])
    cases i <;> simp_all [ProperGate, run]

theorem run_basis_phase (p : Program) (hp : ProperProgram p)
    (x : BasisState) (a b : Bool) (m : List Bool) :
    (run p m ⟨a,x⟩).basis = (run p [] ⟨b,x⟩).basis := by
  induction p generalizing x with
  | nil => rfl
  | cons i p ih =>
    have hi := hp i (by simp)
    have ht : ProperProgram p := fun j hj => hp j (by simp [hj])
    cases i <;> simp_all [ProperGate, run]

/-- Finite basis action of the actual interpreter. -/
def eval (n : Nat) (p : Program) (x : Bits n) : Bits n :=
  restrict n (run p [] ⟨false,extend x⟩).basis

theorem extend_eval (n : Nat) (p : Program)
    (hw : wires p ⊆ Finset.range n) (x : Bits n) :
    extend (eval n p x) = (run p [] ⟨false,extend x⟩).basis := by
  funext w
  by_cases h : w < n
  · simp [extend, eval, restrict, h]
  · have hn : w ∉ wires p := fun hm => h (Finset.mem_range.mp (hw hm))
    rw [run_preserves_outside p [] ⟨false,extend x⟩ w hn]
    simp [extend, h]

theorem reverse_eval (n : Nat) (p : Program) (hp : ProperProgram p)
    (hw : wires p ⊆ Finset.range n) (x : Bits n) :
    eval n p.reverse (eval n p x) = x := by
  change restrict n (run p.reverse [] ⟨false,extend (eval n p x)⟩).basis = x
  rw [extend_eval n p hw]
  have hs : (⟨false, (run p [] ⟨false,extend x⟩).basis⟩ : State) =
      run p [] ⟨false,extend x⟩ := by
    have h := run_phase p hp ⟨false,extend x⟩ []
    cases he : run p [] ⟨false,extend x⟩ with
    | mk ph bs => simp_all
  rw [hs, run_reverse_proper p hp, restrict_extend]

/-- Invertibility follows from gate properness and finite support. -/
def permutation (n : Nat) (p : Program) (hp : ProperProgram p)
    (hw : wires p ⊆ Finset.range n) : Bits n ≃ Bits n where
  toFun := eval n p
  invFun := eval n p.reverse
  left_inv := reverse_eval n p hp hw
  right_inv := by
    intro x
    simpa using reverse_eval n p.reverse (properProgram_reverse p hp)
      (by simpa [wires_reverse] using hw) x

/-- The unique linear extension of the interpreter basis permutation. -/
noncomputable def unitary (n : Nat) (p : Program) (hp : ProperProgram p)
    (hw : wires p ⊆ Finset.range n) :
    EuclideanSpace ℂ (Bits n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bits n) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (permutation n p hp hw)

theorem unitary_basis (n : Nat) (p : Program) (hp : ProperProgram p)
    (hw : wires p ⊆ Finset.range n) (x : Bits n) :
    unitary n p hp hw (EuclideanSpace.single x 1) =
      EuclideanSpace.single (eval n p x) 1 := by
  exact EuclideanSpace.piLpCongrLeft_single (permutation n p hp hw) x 1

theorem run_eq (n : Nat) (p : Program) (hp : ProperProgram p)
    (hw : wires p ⊆ Finset.range n) (x : Bits n) (phase : Bool) (m : List Bool) :
    run p m ⟨phase,extend x⟩ = ⟨phase,extend (eval n p x)⟩ := by
  have hp' := run_phase p hp ⟨phase,extend x⟩ m
  have hb := run_basis_phase p hp (extend x) phase false m
  rw [← extend_eval n p hw x] at hb
  cases he : run p m ⟨phase,extend x⟩ with
  | mk ph bs => simp_all

theorem eval_append (n : Nat) (p q : Program) (hp : ProperProgram p)
    (hw : wires p ⊆ Finset.range n) (x : Bits n) :
    eval n (p ++ q) x = eval n q (eval n p x) := by
  change restrict n (run (p ++ q) [] ⟨false,extend x⟩).basis = _
  rw [run_append]
  simp only [List.drop_nil, List.take_nil]
  rw [run_eq n p hp hw]
  rfl

theorem unitary_apply (n : Nat) (p : Program) (hp : ProperProgram p)
    (hw : wires p ⊆ Finset.range n)
    (ψ : EuclideanSpace ℂ (Bits n)) (x : Bits n) :
    unitary n p hp hw ψ x = ψ (eval n p.reverse x) := rfl

theorem unitary_norm (n : Nat) (p : Program) (hp : ProperProgram p)
    (hw : wires p ⊆ Finset.range n) (ψ : EuclideanSpace ℂ (Bits n)) :
    ‖unitary n p hp hw ψ‖ = ‖ψ‖ :=
  (unitary n p hp hw).norm_map ψ

theorem unitary_append (n : Nat) (p q : Program)
    (hp : ProperProgram p) (hq : ProperProgram q)
    (hwp : wires p ⊆ Finset.range n) (hwq : wires q ⊆ Finset.range n)
    (ψ : EuclideanSpace ℂ (Bits n)) :
    unitary n (p ++ q) ((properProgram_append p q).mpr ⟨hp,hq⟩)
      (by simpa [wires_append] using Finset.union_subset hwp hwq) ψ =
    unitary n q hq hwq (unitary n p hp hwp ψ) := by
  ext x
  simp only [unitary_apply, List.reverse_append]
  rw [eval_append n q.reverse p.reverse (properProgram_reverse q hq)
    (by simpa [wires_reverse] using hwq)]

theorem unitary_reverse (n : Nat) (p : Program) (hp : ProperProgram p)
    (hw : wires p ⊆ Finset.range n) (ψ : EuclideanSpace ℂ (Bits n)) :
    unitary n p.reverse (properProgram_reverse p hp)
      (by simpa [wires_reverse] using hw) (unitary n p hp hw ψ) = ψ := by
  ext x
  simp only [unitary_apply, List.reverse_reverse]
  rw [reverse_eval n p hp hw]

theorem eval_X (n : Nat) (t : Fin n) (x : Bits n) :
    eval n [.X t.val] x = Function.update x t (!x t) := by
  funext w
  simp [eval, restrict, run, writeBit, extend, Function.update, Fin.ext_iff]

theorem eval_CX (n : Nat) (c t : Fin n) (x : Bits n) :
    eval n [.CX c.val t.val] x = Function.update x t (x t ^^ x c) := by
  funext w
  simp [eval, restrict, run, writeBit, extend, Function.update, Fin.ext_iff]

theorem eval_CCX (n : Nat) (a b t : Fin n) (x : Bits n) :
    eval n [.CCX a.val b.val t.val] x =
      Function.update x t (x t ^^ (x a && x b)) := by
  funext w
  simp [eval, restrict, run, writeBit, extend, Function.update, Fin.ext_iff]

noncomputable def linear (n : Nat) (p : Program) (hp : ProperProgram p)
    (hw : wires p ⊆ Finset.range n) :
    EuclideanSpace ℂ (Bits n) →L[ℂ] EuclideanSpace ℂ (Bits n) :=
  (unitary n p hp hw).toContinuousLinearEquiv.toContinuousLinearMap

/-- A good-basis equality extends to the entire good subspace by linearity.
This lemma does not interpret a measurement or assign probabilities to tapes. -/
theorem good_subspace_of_basis {X H : Type*} [Fintype X] [DecidableEq X]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (actual ideal : EuclideanSpace ℂ X →L[ℂ] H) (bad : Finset X)
    (hgood : ∀ x, x ∉ bad →
      actual (EuclideanSpace.single x 1) = ideal (EuclideanSpace.single x 1))
    (v : EuclideanSpace ℂ X) :
    actual (v - FailureBudget.badPart bad v) =
      ideal (v - FailureBudget.badPart bad v) := by
  let w := v - FailureBudget.badPart bad v
  have decomp : ∑ x, w x • EuclideanSpace.single x 1 = w := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
      using (EuclideanSpace.basisFun X ℂ).sum_repr w
  change actual w = ideal w
  rw [← decomp, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ bad
  · have hz : w x = 0 := by simp [w, FailureBudget.badPart, hx]
    simp [hz]
  · simp only [map_smul, hgood x hx]

/-- Sufficient obligations for the approved quantum contract for a proper,
measurement-free program. The actual map is fixed by its interpreter. -/
theorem budget_of_basis (n : Nat) (p : Program) (hp : ProperProgram p)
    (hw : wires p ⊆ Finset.range n)
    (ideal : EuclideanSpace ℂ (Bits n) →L[ℂ] EuclideanSpace ℂ (Bits n))
    (μ : FailureBudget.InputLaw (Bits n)) (bad : Finset (Bits n)) (ε : ℝ)
    (he : 0 ≤ ε) (hlt : ε < 1) (hm : μ.mass bad ≤ ε)
    (hi : ∀ v, ‖ideal v‖ = ‖v‖)
    (hg : ∀ x, x ∉ bad →
      EuclideanSpace.single (eval n p x) 1 = ideal (EuclideanSpace.single x 1)) :
    FailureBudget.QuantumBudget (linear n p hp hw) ideal μ bad ε := by
  have ha : ∀ v, ‖linear n p hp hw v‖ = ‖v‖ := unitary_norm n p hp hw
  refine ⟨he, hlt, hm, ha, hi, ?_⟩
  refine ⟨fun v => le_of_eq (ha v), fun v => le_of_eq (hi v), ?_⟩
  apply good_subspace_of_basis
  intro x hx
  exact (unitary_basis n p hp hw x).trans (hg x hx)

/-- The ideal basis permutation is chosen by the mathematical operation,
independently of the implementation. -/
noncomputable def idealLinear {n : Nat} (e : Bits n ≃ Bits n) :
    EuclideanSpace ℂ (Bits n) →L[ℂ] EuclideanSpace ℂ (Bits n) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toContinuousLinearEquiv.toContinuousLinearMap

/-- All-tape interpreter agreement now implies a quantum budget for embedded
proper gate-only programs. Measurements remain explicitly outside this theorem. -/
theorem budget_of_recorded (n : Nat) (p : Program) (hp : ProperProgram p)
    (hw : wires p ⊆ Finset.range n) (e : Bits n ≃ Bits n)
    (μ : FailureBudget.InputLaw (Bits n)) (bad : Finset (Bits n)) (ε : ℝ)
    (he : 0 ≤ ε) (hlt : ε < 1) (hm : μ.mass bad ≤ ε)
    (hr : FailureBudget.RecordedAgreement (embedRecorded p)
      extend (fun x => extend (e x)) bad) :
    FailureBudget.QuantumBudget (linear n p hp hw) (idealLinear e) μ bad ε := by
  apply budget_of_basis n p hp hw (idealLinear e) μ bad ε he hlt hm
  · intro v
    exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map v
  · intro x hx
    have hs := hr x hx false []
    simp only [runWithTape_embedRecorded, List.drop_zero] at hs
    have hb := congrArg (fun s : State => restrict n s.basis) hs
    change eval n p x = restrict n (extend (e x)) at hb
    rw [restrict_extend] at hb
    change EuclideanSpace.single (eval n p x) 1 =
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (EuclideanSpace.single x 1)
    rw [EuclideanSpace.piLpCongrLeft_single, hb]

end ECDSAAdd.FiniteUnitary
