import ECDSAAdd.Arithmetic.InverseQuotientRecorded

namespace ECDSAAdd.Arithmetic.InverseProductRecorded
open Secp256k1

abbrev InverseContract := InverseQuotientRecorded.InverseContract

def program (inv : RecordedProgram) (c : Wire) (M : MontLayout) (den : List Wire) :
    RecordedProgram :=
  recordedThen (recordedThen inv (embedRecorded (InverseQuotientCore.program c (InverseQuotientCore.denView M den) M.x))) inv

private theorem away (c : Wire) (M : MontLayout) (den : List Wire)
    (hn : (c :: den ++ M.wires).Nodup) (q : Wire) (hq : q ∈ M.x) :
    q ≠ c ∧ q ∉ den ∧ q ∉ M.y ∧ q ∉ M.out ∧ q ∉ M.work := by
  have h := List.nodup_iff_count.mp hn q
  have hx := List.count_pos_iff.mpr hq
  simp only [MontLayout.wires,List.count_cons,List.count_append] at h
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro e; subst q; simp only [beq_self_eq_true,ite_true] at h; omega
  all_goals intro hh; have hh' := List.count_pos_iff.mpr hh; omega

/-- Compute the inverse, execute the actual quotient core, then invoke the same
XOR oracle to clear it. Every non-numerator wire and the phase are restored. -/
theorem states (inv : RecordedProgram) (c : Wire) (M : MontLayout) (den work : List Wire)
    (safe : Fp → Bool → Prop) (hc : InverseContract inv c den M.x work safe)
    (hn : (c :: den ++ M.wires).Nodup) (hw : M.Widths) (hd : den.length = 257)
    (hwork : ∀ q, q ∈ work → q ∉ M.x ∧ q ∉ M.y)
    (B : Bool) (X Y : Fp) (hsafe : safe X B) (hX : B = true → X ≠ 0)
    (s s₁ s₂ s₃ : State) (m₁ m₂ m₃ : List Bool)
    (hb : s.basis c = B) (hx : regValue den s.basis = X.val)
    (hi : regValue M.x s.basis = 0) (hy : regValue M.y s.basis = Y.val)
    (ht : regValue M.out s.basis = 0) (hz : regValue M.work s.basis = 0)
    (hclean : regValue work s.basis = 0)
    (h₁ : runWithTape inv m₁ 0 s = s₁)
    (h₂ : run (InverseQuotientCore.program c (InverseQuotientCore.denView M den) M.x) m₂ s₁ = s₂)
    (h₃ : runWithTape inv m₃ 0 s₂ = s₃) :
    s₃.phase = s.phase ∧
    regValue M.y s₃.basis = (if B then Y*X else Y).val ∧
    ∀ q, q ∉ M.y → s₃.basis q = s.basis q := by
  have a := hc B X hsafe s m₁ hb hx hclean
  rw [h₁,hi,Nat.zero_xor] at a
  obtain ⟨ph₁,iv₁,f₁⟩ := a
  have preserve (r : List Wire) (hr : ∀ q, q ∈ r → q ∉ M.x) :
      regValue r s₁.basis = regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => f₁ q (hr q hq))
  have bc₁ : s₁.basis c = B := (f₁ c (fun hh => (away c M den hn c hh).1 rfl)).trans hb
  have dx₁ := (preserve den (fun q hq hh => (away c M den hn q hh).2.1 hq)).trans hx
  have yy₁ := (preserve M.y (fun q hq hh => (away c M den hn q hh).2.2.1 hq)).trans hy
  have tt₁ := (preserve M.out (fun q hq hh => (away c M den hn q hh).2.2.2.1 hq)).trans ht
  have wz₁ := (preserve M.work (fun q hq hh => (away c M den hn q hh).2.2.2.2 hq)).trans hz
  let I : Fp := if B then X⁻¹ else 0
  have nd : (c :: M.x ++ (InverseQuotientCore.denView M den).wires).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    change List.count q (c :: M.x ++ (den ++ M.y ++ M.out ++ M.work)) ≤ 1
    simp only [MontLayout.wires,List.count_cons,List.count_append] at h ⊢; omega
  have hw' : (InverseQuotientCore.denView M den).Widths := ⟨hd,hw.y,hw.out,hw.first,hw.z,hw.hZ⟩
  have hi0 : B = true → I ≠ 0 := by intro h; simpa [I,h] using inv_ne_zero (hX h)
  have hfac : B = true → X = I⁻¹ := by intro h; simp [I,h]
  have core := InverseQuotientCore.correct_factor c (InverseQuotientCore.denView M den)
    M.x nd hw' hw.x B I Y X hfac hi0 s₁ m₂ bc₁ iv₁ dx₁ yy₁ tt₁ wz₁
  rw [h₂] at core
  have yprod : (if B then Y/I else Y).val = (if B then Y*X else Y).val := by
    cases B <;> simp [I,div_eq_mul_inv]
  rw [yprod] at core
  obtain ⟨ph₂,yy₂,f₂⟩ := core
  have nd := List.nodup_iff_count.mp hn
  have yc : c ∉ M.y := by
    intro hh; have h := nd c; have hy' := List.count_pos_iff.mpr hh
    simp only [MontLayout.wires,List.count_cons,List.count_append,beq_self_eq_true,ite_true] at h; omega
  have dy (q : Wire) (hq : q ∈ den) : q ∉ M.y := by
    intro hh; have h := nd q; have hd' := List.count_pos_iff.mpr hq
    have hy' := List.count_pos_iff.mpr hh
    simp only [MontLayout.wires,List.count_cons,List.count_append] at h; omega
  have bc₂ := (f₂ c yc).trans bc₁
  have dx₂ := (regValue_congr den _ _ (fun q hq => f₂ q (dy q hq))).trans dx₁
  have wi₂ : regValue work s₂.basis = 0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hclean
    intro q hq
    exact (f₂ q (hwork q hq).2).trans (f₁ q (hwork q hq).1)
  have iv₂ : regValue M.x s₂.basis = (if B then X⁻¹ else 0).val :=
    (regValue_congr _ _ _ (fun q hq => f₂ q (away c M den hn q hq).2.2.1)).trans iv₁
  have a₃ := hc B X hsafe s₂ m₃ bc₂ dx₂ wi₂
  rw [h₃,iv₂,Nat.xor_self] at a₃
  obtain ⟨ph₃,iv₃,f₃⟩ := a₃
  refine ⟨ph₃.trans (ph₂.trans ph₁), ?_, ?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => f₃ q
      (fun hh => (away c M den hn q hh).2.2.1 hq))).trans yy₂
  · intro q hqy
    by_cases hqi : q ∈ M.x
    · exact (regValue_eq_iff M.x s₃.basis s.basis).mp (iv₃.trans hi.symm) q hqi
    · exact (f₃ q hqi).trans ((f₂ q hqy).trans (f₁ q hqi))

theorem correct (inv : RecordedProgram) (c : Wire) (M : MontLayout) (den work : List Wire)
    (safe : Fp → Bool → Prop) (hc : InverseContract inv c den M.x work safe)
    (hn : (c :: den ++ M.wires).Nodup) (hw : M.Widths) (hd : den.length = 257)
    (hwork : ∀ q, q ∈ work → q ∉ M.x ∧ q ∉ M.y)
    (B : Bool) (X Y : Fp) (hsafe : safe X B) (hX : B = true → X ≠ 0)
    (s : State) (m : List Bool)
    (hb : s.basis c = B) (hx : regValue den s.basis = X.val)
    (hi : regValue M.x s.basis = 0) (hy : regValue M.y s.basis = Y.val)
    (ht : regValue M.out s.basis = 0) (hz : regValue M.work s.basis = 0)
    (hclean : regValue work s.basis = 0)
 :
    (runWithTape (program inv c M den) m 0 s).phase = s.phase ∧
    regValue M.y (runWithTape (program inv c M den) m 0 s).basis = (if B then Y*X else Y).val ∧
    ∀ q, q ∉ M.y → (runWithTape (program inv c M den) m 0 s).basis q = s.basis q := by
  simp only [program,recordedThen_run,runWithTape_embedRecorded,List.drop_zero]
  exact states inv c M den work safe hc hn hw hd hwork B X Y hsafe hX s _ _ _ m
    (m.drop (recordedMeasurementCount inv))
    (m.drop (recordedMeasurementCount (recordedThen inv
      (embedRecorded (InverseQuotientCore.program c (InverseQuotientCore.denView M den) M.x)))))
    hb hx hi hy ht hz hclean rfl rfl rfl

attribute [local irreducible] InverseQuotientCore.program

theorem wellFormed (inv : RecordedProgram) (c : Wire) (M : MontLayout) (den : List Wire)
    (h : RecordedWellFormedAt 0 inv) : RecordedWellFormedAt 0 (program inv c M den) :=
  recordedThen_wellFormed _ _
    (recordedThen_wellFormed _ _ h (embedRecorded_wellFormed _ _)) h

theorem support (inv : RecordedProgram) (c : Wire) (M : MontLayout) (den : List Wire) :
    recordedWires (program inv c M den) =
      recordedWires inv ∪ wires (InverseQuotientCore.program c (InverseQuotientCore.denView M den) M.x) := by
  simp only [program,recordedThen_wires,embedRecorded_wires]
  ext q; simp only [Finset.mem_union]; tauto

theorem counts (inv : RecordedProgram) (c : Wire) (M : MontLayout) (den : List Wire) :
    recordedToffoliCount (program inv c M den) = 2 * recordedToffoliCount inv +
      toffoliCount (InverseQuotientCore.program c (InverseQuotientCore.denView M den) M.x) ∧
    recordedMeasurementCount (program inv c M den) = 2 * recordedMeasurementCount inv +
      measurementCount (InverseQuotientCore.program c (InverseQuotientCore.denView M den) M.x) := by
  simp only [program,(recordedThen_counts _ _).1,(recordedThen_counts _ _).2,
    (embedRecorded_counts _).1,(embedRecorded_counts _).2]
  omega

end ECDSAAdd.Arithmetic.InverseProductRecorded
