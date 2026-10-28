import ECDSAAdd.Framework.RecordedMeasurement
import Mathlib.Data.Fintype.BigOperators

/-! Finite coherent semantics with persistent measurement records.
The typed Circuit carries input/output record counts. Its program erasure is
well formed and bounded to n data wires. Every constructor has a concrete
isometry; kernel computes interpreter-derived primitive amplitudes and sums
intermediate configurations for sequencing. Every bounded well-formed stream of physical instructions has such a typing.
A closed full-tape runWithTape formula and a RecordedAgreement-to-budget
corollary are separate obligations.
-/

namespace ECDSAAdd.RecordedQuantum

noncomputable def subtypeLinear {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] :
    EuclideanSpace ℂ {x // P x} →ₗ[ℂ] EuclideanSpace ℂ X where
  toFun ψ := WithLp.toLp 2 (fun x => if h : P x then ψ ⟨x,h⟩ else 0)
  map_add' ψ φ := by ext x; by_cases h : P x <;> simp [h]
  map_smul' c ψ := by ext x; by_cases h : P x <;> simp [h]

theorem subtype_norm {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P]
    (ψ : EuclideanSpace ℂ {x // P x}) : ‖subtypeLinear P ψ‖ = ‖ψ‖ := by
  have hs : ‖subtypeLinear P ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [← Fintype.sum_subtype_add_sum_subtype P]
    simp only [subtypeLinear, LinearMap.coe_mk, AddHom.coe_mk]
    have hz : (∑ x : {x // ¬ P x},
        ‖(if h : P x.val then ψ ⟨x.val,h⟩ else 0 : ℂ)‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      simp [x.property]
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro x _
    simp [x.property]

  nlinarith [norm_nonneg (subtypeLinear P ψ), norm_nonneg ψ]

noncomputable def subtypeIsometry {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] :
    EuclideanSpace ℂ {x // P x} →ₗᵢ[ℂ] EuclideanSpace ℂ X where
  toLinearMap := subtypeLinear P
  norm_map' := subtype_norm P

noncomputable def liftLinear {X Y R : Type*} [Fintype X] [Fintype Y] [Fintype R]
    (f : EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ Y) :
    EuclideanSpace ℂ (X × R) →ₗ[ℂ] EuclideanSpace ℂ (Y × R) where
  toFun ψ := WithLp.toLp 2 (fun yr => f (WithLp.toLp 2 (fun x => ψ (x,yr.2))) yr.1)
  map_add' ψ φ := by
    ext ⟨y,r⟩
    change f ((WithLp.toLp 2 (fun x => ψ (x,r))) +
      (WithLp.toLp 2 (fun x => φ (x,r)))) y = _
    rw [map_add]
    rfl
  map_smul' c ψ := by
    ext ⟨y,r⟩
    change f (c • (WithLp.toLp 2 (fun x => ψ (x,r)))) y = _
    rw [map_smul]
    rfl

theorem lift_norm {X Y R : Type*} [Fintype X] [Fintype Y] [Fintype R]
    (f : EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ Y)
    (ψ : EuclideanSpace ℂ (X × R)) : ‖liftLinear f ψ‖ = ‖ψ‖ := by
  have hs : ‖liftLinear f ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro r _
    change (∑ y, ‖f (WithLp.toLp 2 (fun x => ψ (x,r))) y‖ ^ 2) = _
    rw [← EuclideanSpace.norm_sq_eq, f.norm_map, EuclideanSpace.norm_sq_eq]
  nlinarith [norm_nonneg (liftLinear f ψ), norm_nonneg ψ]

noncomputable def liftIsometry {X Y R : Type*} [Fintype X] [Fintype Y] [Fintype R]
    (f : EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ Y) :
    EuclideanSpace ℂ (X × R) →ₗᵢ[ℂ] EuclideanSpace ℂ (Y × R) where
  toLinearMap := liftLinear f
  norm_map' := lift_norm f

theorem linear_apply_sum {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (f : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ Y)
    (ψ : EuclideanSpace ℂ X) (y : Y) :
    f ψ y = ∑ x, ψ x * f (EuclideanSpace.single x 1) y := by
  have decomp : ∑ x, ψ x • EuclideanSpace.single x 1 = ψ := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
      using (EuclideanSpace.basisFun X ℂ).sum_repr ψ
  conv_lhs => rw [← decomp, map_sum]
  simp [map_smul]

open FiniteUnitary RecordedMeasurement

/-- The fresh outcome is appended, so absolute old ordinals do not move. -/
def appendRecord (k : Nat) : (Bool × (Fin k → Bool)) ≃ (Fin (k+1) → Bool) where
  toFun mr := Fin.snoc mr.2 mr.1
  invFun r := (r (Fin.last k), fun j => r j.castSucc)
  left_inv mr := by cases mr; simp
  right_inv r := by funext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp

@[simp] theorem appendRecord_old (k : Nat) (m : Bool) (r : Fin k → Bool) (j : Fin k) :
    appendRecord k (m,r) j.castSucc = r j := by simp [appendRecord]

@[simp] theorem appendRecord_new (k : Nat) (m : Bool) (r : Fin k → Bool) :
    appendRecord k (m,r) (Fin.last k) = m := by simp [appendRecord]

def measuredLabels (n k : Nat) (t : Fin n) :
    ((Bool × Cleared n t) × (Fin k → Bool)) ≃
      {xr : Bits n × (Fin (k+1) → Bool) // xr.1 t = false} where
  toFun v := ⟨(v.1.2.val, appendRecord k (v.1.1,v.2)),v.1.2.property⟩
  invFun v := ((v.val.2 (Fin.last k),⟨v.val.1,v.property⟩),
    fun j => v.val.2 j.castSucc)
  left_inv v := by rcases v with ⟨⟨m,z⟩,r⟩; simp [appendRecord]
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (appendRecord k).apply_symm_apply v.val.2

noncomputable def measurement (n k : Nat) (t : Fin n) (c0 c1 : List Correction) :
    EuclideanSpace ℂ (Bits n × (Fin k → Bool)) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits n × (Fin (k+1) → Bool)) :=
  (subtypeIsometry (fun xr : Bits n × (Fin (k+1) → Bool) => xr.1 t = false)).comp
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (measuredLabels n k t)).toLinearIsometry.comp
      (liftIsometry (measure n t c0 c1)))

theorem measurement_norm (n k : Nat) (t : Fin n) (c0 c1 : List Correction)
    (ψ : EuclideanSpace ℂ (Bits n × (Fin k → Bool))) :
    ‖measurement n k t c0 c1 ψ‖ = ‖ψ‖ := (measurement n k t c0 c1).norm_map ψ

theorem measurement_reset (n k : Nat) (t : Fin n) (c0 c1 : List Correction)
    (ψ : EuclideanSpace ℂ (Bits n × (Fin k → Bool)))
    (x : Bits n) (r : Fin (k+1) → Bool) (h : x t ≠ false) :
    measurement n k t c0 c1 ψ (x,r) = 0 := by
  simp [measurement, subtypeIsometry, subtypeLinear, h]

theorem measurement_apply (n k : Nat) (t : Fin n) (c0 c1 : List Correction)
    (ψ : EuclideanSpace ℂ (Bits n × (Fin k → Bool)))
    (x : Bits n) (r : Fin (k+1) → Bool) :
    measurement n k t c0 c1 ψ (x,r) =
      if h : x t = false then
        measure n t c0 c1 (WithLp.toLp 2 (fun y => ψ (y,fun j => r j.castSucc)))
          (r (Fin.last k),⟨x,h⟩)
      else 0 := by
  rfl

theorem slice_single {X R : Type*} [Fintype X] [Fintype R] [DecidableEq X]
    [DecidableEq R] (x : X) (r s : R) :
    (WithLp.toLp 2 (fun y => (EuclideanSpace.single (x,r) 1 :
      EuclideanSpace ℂ (X × R)) (y,s))) =
      if s = r then EuclideanSpace.single x 1 else 0 := by
  ext y
  by_cases h : s = r
  · subst s; simp [EuclideanSpace.single_apply]
  · simp [EuclideanSpace.single_apply, h, Prod.mk.injEq]

theorem lift_single {X Y R : Type*} [Fintype X] [Fintype Y] [Fintype R]
    [DecidableEq X] [DecidableEq R]
    (f : EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ Y)
    (x : X) (y : Y) (r s : R) :
    liftIsometry f (EuclideanSpace.single (x,r) 1) (y,s) =
      if s = r then f (EuclideanSpace.single x 1) y else 0 := by
  change f (WithLp.toLp 2 (fun z => (EuclideanSpace.single (x,r) 1 :
    EuclideanSpace ℂ (X × R)) (z,s))) y = _
  rw [slice_single]
  split <;> simp_all

theorem measurement_single (n k : Nat) (t : Fin n) (c0 c1 : List Correction)
    (x y : Bits n) (r : Fin k → Bool) (s : Fin (k+1) → Bool) :
    measurement n k t c0 c1 (EuclideanSpace.single (x,r) 1) (y,s) =
      if (fun j => s j.castSucc) = r ∧ y = (clear t x).val then
        sign ((measureAndCorrect t.val c0 c1 (s (Fin.last k)) ⟨false,extend x⟩).phase) /
          (Real.sqrt 2 : ℂ)
      else 0 := by
  rw [measurement_apply, slice_single]
  by_cases hr : (fun j : Fin k => s j.castSucc) = r
  · simp only [hr, ↓reduceIte, true_and]
    by_cases hy : y t = false
    · simp only [hy, ↓reduceDIte, measure_single]
      congr 1
      exact propext Subtype.ext_iff
    · have hn : y ≠ (clear t x).val := by
        intro he; apply hy; rw [he]; exact (clear t x).property
      simp [hy,hn]
  · simp [hr]

/-- Circuit typing records the number of outcomes available at each boundary. -/
inductive Circuit (n : Nat) : Nat → Nat → Type where
  | gates {k : Nat} (p : Program) (hp : ProperProgram p)
      (hw : wires p ⊆ Finset.range n) : Circuit n k k
  | measure {k : Nat} (t : Fin n) (c0 c1 : List Correction)
      (hw0 : correctionWires c0 ⊆ Finset.range n)
      (hw1 : correctionWires c1 ⊆ Finset.range n) : Circuit n k (k+1)
  | saved {k : Nat} (j : Fin k) (cs : List Correction)
      (hw : correctionWires cs ⊆ Finset.range n) : Circuit n k k
  | seq {k l m : Nat} (a : Circuit n k l) (b : Circuit n l m) : Circuit n k m

namespace Circuit

def program {n k l : Nat} : Circuit n k l → RecordedProgram
  | .gates p _ _ => embedRecorded p
  | .measure t c0 c1 _ _ => [.gate (.measureX t.val c0 c1)]
  | .saved j cs _ => [.phaseFromRecord j.val cs]
  | .seq a b => a.program ++ b.program

noncomputable def semantics {n k l : Nat} : Circuit n k l →
    (EuclideanSpace ℂ (Bits n × (Fin k → Bool)) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Bits n × (Fin l → Bool)))
  | .gates p hp hw => liftIsometry (unitary n p hp hw).toLinearIsometry
  | .measure t c0 c1 _ _ => measurement n _ t c0 c1
  | .saved j cs _ => savedCorrection n _ j cs
  | .seq a b => b.semantics.comp a.semantics

theorem norm {n k l : Nat} (p : Circuit n k l)
    (ψ : EuclideanSpace ℂ (Bits n × (Fin k → Bool))) :
    ‖p.semantics ψ‖ = ‖ψ‖ := p.semantics.norm_map ψ

theorem semantics_seq {n k l m : Nat} (a : Circuit n k l) (b : Circuit n l m) :
    (seq a b).semantics = b.semantics.comp a.semantics := rfl

/-- Interpreter-derived primitive amplitudes, composed by summing intermediate
configurations. The sum is coherent: probabilities are not composed here. -/
noncomputable def kernel {n k l : Nat} (p : Circuit n k l)
    (input : Bits n × (Fin k → Bool)) (output : Bits n × (Fin l → Bool)) : ℂ :=
  match p with
  | .gates code _ _ =>
      if output.2 = input.2 ∧ output.1 = eval n code input.1 then 1 else 0
  | .measure t c0 c1 _ _ =>
      if (fun j => output.2 j.castSucc) = input.2 ∧ output.1 = (clear t input.1).val then
        sign ((measureAndCorrect t.val c0 c1 (output.2 (Fin.last _))
          ⟨false,extend input.1⟩).phase) / (Real.sqrt 2 : ℂ)
      else 0
  | .saved j cs _ =>
      if output = input then sign ((runWithTape [.phaseFromRecord j.val cs]
        (List.ofFn input.2) k ⟨false,extend input.1⟩).phase) else 0
  | .seq a b => ∑ mid, a.kernel input mid * b.kernel mid output

theorem kernel_eq {n k l : Nat} (p : Circuit n k l)
    (input : Bits n × (Fin k → Bool)) (output : Bits n × (Fin l → Bool)) :
    p.semantics (EuclideanSpace.single input 1) output = p.kernel input output := by
  induction p with
  | gates code hp hw =>
    rcases input with ⟨x,r⟩; rcases output with ⟨y,s⟩
    change liftIsometry _ _ _ = _
    rw [lift_single]
    change (if s = r then unitary n code hp hw (EuclideanSpace.single x 1) y else 0) = _
    rw [unitary_basis]
    simp [kernel, EuclideanSpace.single_apply, ite_and]
  | measure t c0 c1 h0 h1 => exact measurement_single _ _ _ _ _ _ _ _ _
  | @saved k j cs hw =>
    change savedCorrection _ _ _ _ _ _ = _
    rw [savedCorrection_single n k j cs input.1 input.2 k]
    simp [kernel, EuclideanSpace.single_apply, mul_ite]
  | seq a b ha hb =>
    change b.semantics.toLinearMap (a.semantics (EuclideanSpace.single input 1)) output = _
    rw [linear_apply_sum b.semantics.toLinearMap]
    simp only [kernel]
    apply Finset.sum_congr rfl
    intro mid _
    simp only [LinearIsometry.coe_toLinearMap, ha, hb]

theorem apply_kernel {n k l : Nat} (p : Circuit n k l)
    (ψ : EuclideanSpace ℂ (Bits n × (Fin k → Bool)))
    (output : Bits n × (Fin l → Bool)) :
    p.semantics ψ output = ∑ input, ψ input * p.kernel input output := by
  change p.semantics.toLinearMap ψ output = _
  rw [linear_apply_sum p.semantics.toLinearMap]
  simp only [LinearIsometry.coe_toLinearMap, kernel_eq]

theorem count {n k l : Nat} (p : Circuit n k l) :
    k + recordedMeasurementCount p.program = l := by
  induction p with
  | gates p hp hw => simp [program, embedRecorded_counts, properProgram_measurementCount p hp]
  | measure t c0 c1 h0 h1 => rfl
  | saved j cs hw => rfl
  | seq a b ha hb =>
    simp only [program, recordedMeasurementCount_append]
    omega

theorem wellFormed {n k l : Nat} (p : Circuit n k l) :
    RecordedWellFormedAt k p.program := by
  induction p with
  | gates p hp hw => exact embedRecorded_wellFormed p _
  | measure t c0 c1 h0 h1 => trivial
  | saved j cs hw => exact ⟨j.isLt, trivial⟩
  | seq a b ha hb =>
    rw [program, RecordedWellFormedAt_append, a.count]
    exact ⟨ha,hb⟩

theorem support {n k l : Nat} (p : Circuit n k l) :
    recordedWires p.program ⊆ Finset.range n := by
  induction p with
  | gates p hp hw => simpa [program, embedRecorded_counts] using hw
  | measure t c0 c1 h0 h1 =>
    simp only [program, recordedWires, RecordedInstr.quantumWires, Instr.wires,
      Finset.union_empty]
    intro x hx
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with (rfl | hx) | hx
    · exact Finset.mem_range.mpr t.isLt
    · exact h0 hx
    · exact h1 hx
  | saved j cs hw => simpa [program, recordedWires, RecordedInstr.quantumWires] using hw
  | seq a b ha hb => simpa only [program, recordedWires_append, Finset.union_subset_iff] using And.intro ha hb

/-- The ideal map includes the same retained record space and must be supplied
independently. Kernel agreement is an explicit obligation, not inferred from
uniform record probabilities. -/
theorem budget_of_kernel {n k l : Nat} (p : Circuit n k l)
    (ideal : EuclideanSpace ℂ (Bits n × (Fin k → Bool)) →L[ℂ]
      EuclideanSpace ℂ (Bits n × (Fin l → Bool)))
    (μ : FailureBudget.InputLaw (Bits n × (Fin k → Bool)))
    (bad : Finset (Bits n × (Fin k → Bool))) (ε : ℝ)
    (he : 0 ≤ ε) (hlt : ε < 1) (hm : μ.mass bad ≤ ε)
    (hi : ∀ v, ‖ideal v‖ = ‖v‖)
    (hg : ∀ x, x ∉ bad → ∀ y,
      p.kernel x y = ideal (EuclideanSpace.single x 1) y) :
    FailureBudget.QuantumBudget p.semantics.toContinuousLinearMap ideal μ bad ε := by
  have ha : ∀ v, ‖p.semantics.toContinuousLinearMap v‖ = ‖v‖ := p.norm
  refine ⟨he,hlt,hm,ha,hi,?_⟩
  refine ⟨fun v => le_of_eq (ha v),fun v => le_of_eq (hi v),?_⟩
  apply good_subspace_of_basis
  intro x hx
  ext y
  exact (p.kernel_eq x y).trans (hg x hx y)

end Circuit
/-- Ordinary gates have no target/control alias. Measurements are admitted. -/
def PhysicalInstr : RecordedInstr → Prop
  | .gate (.measureX _ _ _) => True
  | .gate i => ProperGate i
  | .phaseFromRecord _ _ => True

theorem realize_instr (n k : Nat) (i : RecordedInstr)
    (hp : PhysicalInstr i) (hf : RecordedWellFormedAt k [i])
    (hw : i.quantumWires ⊆ Finset.range n) :
    ∃ l, ∃ c : Circuit n k l, c.program = [i] := by
  cases i with
  | phaseFromRecord j cs =>
    exact ⟨k,.saved ⟨j,hf.1⟩ cs hw,rfl⟩
  | gate i =>
    cases i with
    | X t => exact ⟨k,.gates [.X t] (by simpa [ProperProgram, PhysicalInstr] using hp)
        (by simpa [wires] using hw),rfl⟩
    | CX a t => exact ⟨k,.gates [.CX a t] (by simpa [ProperProgram, PhysicalInstr] using hp)
        (by simpa [wires] using hw),rfl⟩
    | CCX a b t => exact ⟨k,.gates [.CCX a b t] (by simpa [ProperProgram, PhysicalInstr] using hp)
        (by simpa [wires] using hw),rfl⟩
    | measureX t c0 c1 =>
      have ht : t < n := Finset.mem_range.mp (hw (by simp [RecordedInstr.quantumWires,Instr.wires]))
      have h0 : correctionWires c0 ⊆ Finset.range n := by
        intro w h; apply hw; simp [RecordedInstr.quantumWires,Instr.wires,h]
      have h1 : correctionWires c1 ⊆ Finset.range n := by
        intro w h; apply hw; simp [RecordedInstr.quantumWires,Instr.wires,h]
      exact ⟨k+1,.measure ⟨t,ht⟩ c0 c1 h0 h1,rfl⟩

theorem realize (n k : Nat) (p : RecordedProgram)
    (hp : ∀ i ∈ p, PhysicalInstr i) (hf : RecordedWellFormedAt k p)
    (hw : recordedWires p ⊆ Finset.range n) :
    ∃ l, ∃ c : Circuit n k l, c.program = p := by
  induction p generalizing k with
  | nil => exact ⟨k,.gates [] (by simp [ProperProgram]) (by simp [wires]),rfl⟩
  | cons i p ih =>
    have hf' : RecordedWellFormedAt k [i] ∧
        RecordedWellFormedAt (k+recordedMeasurementCount [i]) p :=
      (RecordedWellFormedAt_append k [i] p).mp hf
    have hi : i.quantumWires ⊆ Finset.range n := fun w h =>
      hw (Finset.mem_union_left _ h)
    obtain ⟨l,a,ha⟩ := realize_instr n k i (hp i (by simp)) hf'.1 hi
    have hl : k+recordedMeasurementCount [i] = l := by rw [← ha]; exact a.count
    rw [hl] at hf'
    obtain ⟨m,b,hb⟩ := ih l (fun j hj => hp j (by simp [hj])) hf'.2
      (fun w h => hw (Finset.mem_union_right _ h))
    exact ⟨m,.seq a b,by simp [Circuit.program,ha,hb]⟩


end ECDSAAdd.RecordedQuantum
