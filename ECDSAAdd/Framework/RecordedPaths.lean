import ECDSAAdd.Framework.RecordedQuantum

/-! Final-record interpreter formula and the measured quantum bridge.
The actual map comes from the typed program, with initially empty records.
The independent ideal is a mathematical permutation tensored with a proved
normalized uniform record state. All-tape RecordedAgreement implies equality
on good inputs, and hence the adopted QuantumBudget and 2*sqrt ε vector bound.
No numerical failure estimate or physical resource bound is asserted here.
-/

namespace ECDSAAdd.RecordedQuantum
open RecordedMeasurement FiniteUnitary

private theorem state_ext {s t : State} (hp : s.phase = t.phase) (hb : s.basis = t.basis) : s = t := by
  cases s; cases t; simp_all

def shiftPhase (b : Bool) (s : State) : State := ⟨b ^^ s.phase,s.basis⟩

theorem correct_shift (cs : List Correction) (ph : Bool) (s : State) :
    correct cs (shiftPhase ph s) = shiftPhase ph (correct cs s) := by
  apply state_ext
  · simp only [shiftPhase]
    rw [correct_phase cs s.basis (ph ^^ s.phase), correct_phase cs s.basis s.phase]
    exact Bool.xor_assoc _ _ _
  · simp [shiftPhase]

theorem measure_shift (t : Wire) (c0 c1 : List Correction) (m ph : Bool) (s : State) :
    measureAndCorrect t c0 c1 m (shiftPhase ph s) =
      shiftPhase ph (measureAndCorrect t c0 c1 m s) := by
  unfold measureAndCorrect
  rw [← correct_shift]
  congr 1
  apply state_ext
  · exact Bool.xor_assoc _ _ _
  · rfl

theorem run_shift (p : Program) (tape : List Bool) (ph : Bool) (s : State) :
    run p tape (shiftPhase ph s) = shiftPhase ph (run p tape s) := by
  induction p generalizing tape s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | X t => simpa only [run,shiftPhase] using ih tape ⟨s.phase,writeBit s.basis t (!s.basis t)⟩
    | CX a t => simpa only [run,shiftPhase] using ih tape ⟨s.phase,writeBit s.basis t (s.basis t ^^ s.basis a)⟩
    | CCX a b t => simpa only [run,shiftPhase] using ih tape ⟨s.phase,writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))⟩
    | measureX t c0 c1 => simp only [run]; rw [measure_shift,ih]

theorem runWithTape_shift (p : RecordedProgram) (tape : List Bool) (k : Nat)
    (ph : Bool) (s : State) :
    runWithTape p tape k (shiftPhase ph s) = shiftPhase ph (runWithTape p tape k s) := by
  induction p generalizing k s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | gate i => simp only [runWithTape]; rw [run_shift,ih]
    | phaseFromRecord j cs =>
      simp only [runWithTape]
      split
      · rw [correct_shift,ih]
      · exact ih k s

theorem drop_head (tape : List Bool) (k : Nat) :
    (tape.drop k).headD false = tape.getD k false := by
  simp [List.getD]

theorem run_one_tape_congr (i : Instr) (a b : List Bool) (k : Nat) (s : State)
    (h : ∀ j < k + measurementCount [i], a.getD j false = b.getD j false) :
    run [i] (a.drop k) s = run [i] (b.drop k) s := by
  cases i <;> simp only [run]
  rw [drop_head,drop_head,h k (by simp [measurementCount])]

theorem runWithTape_tape_congr (p : RecordedProgram) (a b : List Bool) (k : Nat)
    (s : State) (hf : RecordedWellFormedAt k p)
    (h : ∀ j < k+recordedMeasurementCount p, a.getD j false = b.getD j false) :
    runWithTape p a k s = runWithTape p b k s := by
  induction p generalizing k s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | gate i =>
      simp only [runWithTape]
      have hi : ∀ j < k+measurementCount [i], a.getD j false = b.getD j false := by
        intro j hj; apply h; simp only [recordedMeasurementCount]; omega
      rw [run_one_tape_congr i a b k s hi]
      apply ih _ _ hf
      intro j hj; apply h; simpa only [recordedMeasurementCount,Nat.add_assoc] using hj
    | phaseFromRecord j cs =>
      simp only [runWithTape]
      have hj := hf.1
      rw [h j (by simp only [recordedMeasurementCount]; omega)]
      apply ih _ _ hf.2
      exact h

def recordPrefix {k l : Nat} (h : k ≤ l) (r : Fin l → Bool) : Fin k → Bool :=
  fun j => r (Fin.castLE h j)

@[simp] theorem prefix_refl {k : Nat} (r : Fin k → Bool) : recordPrefix (Nat.le_refl k) r = r := rfl

theorem prefix_trans {k l m : Nat} (h : k ≤ l) (g : l ≤ m) (r : Fin m → Bool) :
    recordPrefix h (recordPrefix g r) = recordPrefix (h.trans g) r := rfl

theorem prefix_getD {k l : Nat} (h : k ≤ l) (r : Fin l → Bool) (j : Nat) (hj : j < k) :
    (List.ofFn (recordPrefix h r)).getD j false = (List.ofFn r).getD j false := by
  simp [List.getD, hj, lt_of_lt_of_le hj h, recordPrefix]

theorem runWithTape_prefix {n k l m : Nat} (c : Circuit n k l) (h : l ≤ m)
    (r : Fin m → Bool) (s : State) :
    runWithTape c.program (List.ofFn (recordPrefix h r)) k s =
      runWithTape c.program (List.ofFn r) k s := by
  apply runWithTape_tape_congr _ _ _ _ _ c.wellFormed
  intro j hj
  rw [c.count] at hj
  exact prefix_getD h r j hj

namespace Circuit

theorem le {n k l : Nat} (c : Circuit n k l) : k ≤ l := by
  have h := c.count; omega

noncomputable def scale {n k l : Nat} : Circuit n k l → ℂ
  | .gates _ _ _ => 1
  | .measure _ _ _ _ _ => 1 / (Real.sqrt 2 : ℂ)
  | .saved _ _ _ => 1
  | .seq a b => a.scale * b.scale

def result {n k l : Nat} (c : Circuit n k l) (r : Fin l → Bool) (x : Bits n) : State :=
  runWithTape c.program (List.ofFn r) k ⟨false,extend x⟩

def resultBits {n k l : Nat} (c : Circuit n k l) (r : Fin l → Bool) (x : Bits n) : Bits n :=
  restrict n (c.result r x).basis

theorem result_extend {n k l : Nat} (c : Circuit n k l) (r : Fin l → Bool) (x : Bits n) :
    extend (c.resultBits r x) = (c.result r x).basis := by
  funext w
  by_cases h : w < n
  · simp [extend,resultBits,restrict,h]
  · have hn : w ∉ recordedWires c.program := fun hm => h (Finset.mem_range.mp (c.support hm))
    have he := runWithTape_preserves_outside c.program (List.ofFn r) k ⟨false,extend x⟩ w hn
    simpa [extend,resultBits,result,h] using he.symm

theorem result_state {n k l : Nat} (c : Circuit n k l) (r : Fin l → Bool) (x : Bits n) :
    c.result r x = ⟨(c.result r x).phase,extend (c.resultBits r x)⟩ := by
  apply state_ext
  · rfl
  · exact (c.result_extend r x).symm

theorem result_seq {n k l m : Nat} (a : Circuit n k l) (b : Circuit n l m)
    (r : Fin m → Bool) (x : Bits n) :
    (a.seq b).result r x =
      shiftPhase (a.result (recordPrefix b.le r) x).phase
        (b.result r (a.resultBits (recordPrefix b.le r) x)) := by
  simp only [result,program,runWithTape_append,a.count]
  rw [← runWithTape_prefix a b.le r ⟨false,extend x⟩]
  change runWithTape b.program (List.ofFn r) l (a.result (recordPrefix b.le r) x) = _
  rw [a.result_state]
  have hs : (⟨(a.result (recordPrefix b.le r) x).phase,
      extend (a.resultBits (recordPrefix b.le r) x)⟩ : State) =
      shiftPhase (a.result (recordPrefix b.le r) x).phase
        ⟨false,extend (a.resultBits (recordPrefix b.le r) x)⟩ := by simp [shiftPhase]
  rw [hs,runWithTape_shift]
  rfl

theorem kernel_final {n k l : Nat} (c : Circuit n k l)
    (input : Bits n × (Fin k → Bool)) (output : Bits n × (Fin l → Bool)) :
    c.kernel input output =
      if recordPrefix c.le output.2 = input.2 ∧ output.1 = c.resultBits output.2 input.1 then
        c.scale * sign (c.result output.2 input.1).phase else 0 := by
  induction c with
  | gates p hp hw =>
    simp [kernel,resultBits,result,program,runWithTape_embedRecorded,
      run_eq n p hp hw,scale,restrict_extend,sign]
  | @saved k j cs hw =>
    by_cases hr : output.2 = input.2
    · rcases input with ⟨x,r⟩; rcases output with ⟨y,s⟩
      dsimp at hr; subst s
      cases hm : r j <;> simp [kernel,resultBits,result,program,scale,runWithTape,
        restrict_extend,Prod.mk.injEq,hm]
    · simp [kernel,resultBits,result,program,hr,Prod.ext_iff]
  | @measure k t c0 c1 h0 h1 =>
    have hpref : recordPrefix (Circuit.measure (k := k) t c0 c1 h0 h1).le output.2 =
        (fun j => output.2 j.castSucc) := rfl
    have hdrop : ((List.ofFn output.2).drop k).headD false = output.2 (Fin.last k) := by
      rw [drop_head]
      simp only [List.getD, List.getElem?_ofFn, Nat.lt_succ_self, ↓reduceDIte, Option.getD_some]
      rfl
    simp only [kernel,hpref,resultBits,result,program,runWithTape,run,hdrop]
    rw [measurement_basis]
    simp only [scale,one_div,measurement_phase]
    simp [clear,mul_comm,div_eq_mul_inv]
  | seq a b ha hb =>
    let middle := (a.resultBits (recordPrefix b.le output.2) input.1, recordPrefix b.le output.2)
    rw [kernel, Finset.sum_eq_single middle]
    · rw [ha,hb]
      simp only [middle, and_true, true_and]
      have hbits : (a.seq b).resultBits output.2 input.1 =
          b.resultBits output.2 (a.resultBits (recordPrefix b.le output.2) input.1) := by
        simp only [resultBits,result_seq,shiftPhase]
      rw [hbits,result_seq]
      simp only [shiftPhase,sign_xor,scale]
      have hpref : recordPrefix (a.seq b).le output.2 =
          recordPrefix a.le (recordPrefix b.le output.2) := rfl
      rw [hpref]
      split <;> split <;> simp_all
      all_goals ring
    · intro mid _ hne
      rw [ha,hb]
      by_cases hr : recordPrefix b.le output.2 = mid.2
      · have hx : mid.1 ≠ a.resultBits mid.2 input.1 := by
          intro hx; apply hne; apply Prod.ext
          · simpa only [middle,hr] using hx
          · exact hr.symm
        simp [hx]
      · simp [hr]
    · simp

theorem scale_count {n k l : Nat} (c : Circuit n k l) :
    c.scale = (1 / (Real.sqrt 2 : ℂ)) ^ recordedMeasurementCount c.program := by
  induction c with
  | gates p hp hw => simp [scale,program,embedRecorded_counts,properProgram_measurementCount p hp]
  | measure t c0 c1 h0 h1 => simp [scale,program,recordedMeasurementCount,measurementCount]
  | saved j cs hw => rfl
  | seq a b ha hb => simp [scale,program,recordedMeasurementCount_append,pow_add,ha,hb]

theorem semantics_eq_of_program_eq {n k l : Nat} (a b : Circuit n k l)
    (h : a.program = b.program) : a.semantics = b.semantics := by
  ext ψ output
  rw [a.apply_kernel,b.apply_kernel]
  apply Finset.sum_congr rfl
  intro input _
  congr 1
  simp only [kernel_final,scale_count,resultBits,result,h]

end Circuit
theorem uniform_scale_norm (l : Nat) :
    (2:ℝ)^l * ‖(1 / (Real.sqrt 2 : ℂ)) ^ l‖ ^ 2 = 1 := by
  have hn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hb : 2 * ‖1 / (Real.sqrt 2 : ℂ)‖^2 = 1 := by
    simp only [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn,
      div_pow,one_pow,h2]
    norm_num
  rw [norm_pow,← pow_mul,Nat.mul_comm l 2,pow_mul,← mul_pow,hb,one_pow]

noncomputable def uniformLinear {X : Type*} [Fintype X] (l : Nat) :
    EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ (X × (Fin l → Bool)) where
  toFun ψ := WithLp.toLp 2 (fun xr => ((1 / (Real.sqrt 2 : ℂ))^l) * ψ xr.1)
  map_add' ψ φ := by ext xr; simp [mul_add]
  map_smul' c ψ := by ext xr; simp [mul_left_comm]

theorem uniform_norm {X : Type*} [Fintype X] (l : Nat) (ψ : EuclideanSpace ℂ X) :
    ‖uniformLinear l ψ‖ = ‖ψ‖ := by
  have hs : ‖uniformLinear l ψ‖^2 = ‖ψ‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    simp only [uniformLinear,LinearMap.coe_mk,AddHom.coe_mk,norm_mul,mul_pow]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [← mul_assoc,uniform_scale_norm,one_mul]
  nlinarith [norm_nonneg (uniformLinear l ψ),norm_nonneg ψ]

noncomputable def uniform {X : Type*} [Fintype X] (l : Nat) :
    EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ (X × (Fin l → Bool)) where
  toLinearMap := uniformLinear l
  norm_map' := uniform_norm l


def emptyLabels (X : Type*) : X ≃ (X × (Fin 0 → Bool)) where
  toFun x := (x,Fin.elim0)
  invFun x := x.1
  left_inv _ := rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext j; exact Fin.elim0 j

noncomputable def emptyInit (X : Type*) [Fintype X] :
    EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ (X × (Fin 0 → Bool)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (emptyLabels X)).toLinearIsometry

noncomputable def actual {n l : Nat} (c : Circuit n 0 l) :
    EuclideanSpace ℂ (Bits n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Bits n × (Fin l → Bool)) :=
  c.semantics.comp (emptyInit (Bits n))

/-- A mathematical permutation with a fresh, independent uniform record state. -/
noncomputable def ideal {n : Nat} (l : Nat) (e : Bits n ≃ Bits n) :
    EuclideanSpace ℂ (Bits n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Bits n × (Fin l → Bool)) :=
  (uniform l).comp (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearIsometry

theorem actual_basis {n l : Nat} (c : Circuit n 0 l) (x : Bits n)
    (output : Bits n × (Fin l → Bool)) :
    actual c (EuclideanSpace.single x 1) output =
      if output.1 = c.resultBits output.2 x then
        c.scale * sign (c.result output.2 x).phase else 0 := by
  change c.semantics ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (emptyLabels (Bits n)))
    (EuclideanSpace.single x 1)) output = _
  rw [EuclideanSpace.piLpCongrLeft_single,c.kernel_eq,c.kernel_final]
  have he : recordPrefix c.le output.2 = (emptyLabels (Bits n) x).2 := by
    funext j; exact Fin.elim0 j
  simp [he,emptyLabels]

theorem ideal_basis {n l : Nat} (e : Bits n ≃ Bits n) (x : Bits n)
    (output : Bits n × (Fin l → Bool)) :
    ideal l e (EuclideanSpace.single x 1) output =
      if output.1 = e x then (1 / (Real.sqrt 2 : ℂ))^l else 0 := by
  change uniform l ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
    (EuclideanSpace.single x 1)) output = _
  rw [EuclideanSpace.piLpCongrLeft_single]
  simp [uniform,uniformLinear,EuclideanSpace.single_apply]

theorem basis_of_recorded {n l : Nat} (c : Circuit n 0 l) (e : Bits n ≃ Bits n)
    (bad : Finset (Bits n))
    (hr : FailureBudget.RecordedAgreement c.program extend (fun x => extend (e x)) bad)
    (x : Bits n) (hx : x ∉ bad) :
    actual c (EuclideanSpace.single x 1) = ideal l e (EuclideanSpace.single x 1) := by
  ext output
  rw [actual_basis,ideal_basis]
  have hs : c.result output.2 x = ⟨false,extend (e x)⟩ := hr x hx false (List.ofFn output.2)
  have hb : c.resultBits output.2 x = e x := by simp [Circuit.resultBits,hs]
  have hc : recordedMeasurementCount c.program = l := by simpa using c.count
  simp [hb,hs,c.scale_count,hc,sign]

theorem budget_of_recorded {n l : Nat} (c : Circuit n 0 l) (e : Bits n ≃ Bits n)
    (μ : FailureBudget.InputLaw (Bits n)) (bad : Finset (Bits n)) (ε : ℝ)
    (he : 0 ≤ ε) (hlt : ε < 1) (hm : μ.mass bad ≤ ε)
    (hr : FailureBudget.RecordedAgreement c.program extend (fun x => extend (e x)) bad) :
    FailureBudget.QuantumBudget (actual c).toContinuousLinearMap
      (ideal l e).toContinuousLinearMap μ bad ε := by
  have ha : ∀ v, ‖(actual c).toContinuousLinearMap v‖ = ‖v‖ := (actual c).norm_map
  have hi : ∀ v, ‖(ideal l e).toContinuousLinearMap v‖ = ‖v‖ := (ideal l e).norm_map
  refine ⟨he,hlt,hm,ha,hi,?_⟩
  refine ⟨fun v => le_of_eq (ha v),fun v => le_of_eq (hi v),?_⟩
  apply good_subspace_of_basis
  exact basis_of_recorded c e bad hr

theorem error_of_recorded {n l : Nat} (c : Circuit n 0 l) (e : Bits n ≃ Bits n)
    (μ : FailureBudget.InputLaw (Bits n)) (bad : Finset (Bits n)) (ε : ℝ)
    (he : 0 ≤ ε) (hlt : ε < 1) (hm : μ.mass bad ≤ ε)
    (hr : FailureBudget.RecordedAgreement c.program extend (fun x => extend (e x)) bad)
    (ψ : EuclideanSpace ℂ (Bits n)) (hn : ‖ψ‖ = 1)
    (matching : ∀ x, ‖ψ x‖ ^ 2 = μ.weight x) :
    ‖actual c ψ - ideal l e ψ‖ ≤ 2 * Real.sqrt ε :=
  (budget_of_recorded c e μ bad ε he hlt hm hr).error_le ψ hn matching

noncomputable def recordMass {n l : Nat} (c : Circuit n 0 l) (ψ : EuclideanSpace ℂ (Bits n))
    (r : Fin l → Bool) : ℝ := ∑ x, ‖actual c ψ (x,r)‖ ^ 2

theorem recordMass_nonneg {n l : Nat} (c : Circuit n 0 l)
    (ψ : EuclideanSpace ℂ (Bits n)) (r : Fin l → Bool) : 0 ≤ recordMass c ψ r := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem recordMass_total {n l : Nat} (c : Circuit n 0 l) (ψ : EuclideanSpace ℂ (Bits n)) :
    ∑ r, recordMass c ψ r = ‖ψ‖ ^ 2 := by
  rw [← (actual c).norm_map ψ,EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type_right]
  rfl

end ECDSAAdd.RecordedQuantum
