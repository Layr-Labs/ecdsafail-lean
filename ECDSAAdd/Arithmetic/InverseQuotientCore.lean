import ECDSAAdd.Arithmetic.MontAdapterFrame
import ECDSAAdd.Arithmetic.SwapLow
import ECDSAAdd.Math.BitcoinPrimes

namespace ECDSAAdd.Arithmetic.InverseQuotientCore
open Secp256k1

/-- Reuse the product workspace with the preserved denominator as multiplier. -/
def denView (M : MontLayout) (den : List Wire) : MontLayout := { M with x := den }

/-- Given a separately computed inverse, form the quotient, exchange it into
Y, and subtract X*(Y/X) to clear the old numerator. This is an actual gate list.
The Montgomery reference workspace is large; no 935-space claim is made. -/
def program (c : Wire) (M : MontLayout) (den : List Wire) : Program :=
  montMulControlledAdd c M p ++
  swapRegisters c (M.y.take 256) (M.out.take 256) ++
  montMulControlledSub c (denView M den) p

private theorem views (c : Wire) (M : MontLayout) (den : List Wire)
    (hn : (c :: den ++ M.wires).Nodup) (hw : M.Widths) (hd : den.length = 257) :
    (c :: M.wires).Nodup ∧ (c :: (denView M den).wires).Nodup ∧
      (denView M den).Widths ∧ (c :: M.y ++ M.out).Nodup := by
  have hcount := List.nodup_iff_count.mp hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply List.nodup_iff_count.mpr
    intro q
    have h := hcount q
    simp only [List.count_cons, List.count_append] at h ⊢
    omega
  · apply List.nodup_iff_count.mpr
    intro q
    have h := hcount q
    change List.count q (c :: den ++ M.y ++ M.out ++ M.work) ≤ 1
    simp only [MontLayout.wires, List.count_cons, List.count_append] at h ⊢
    omega
  · exact ⟨hd,hw.y,hw.out,hw.first,hw.z,hw.hZ⟩
  · apply List.nodup_iff_count.mpr
    intro q
    have h := hcount q
    simp only [MontLayout.wires, List.count_cons, List.count_append] at h ⊢
    omega

private theorem den_away (c : Wire) (M : MontLayout) (den : List Wire)
    (hn : (c :: den ++ M.wires).Nodup) (q : Wire) (hq : q ∈ den) :
    q ∉ M.y ∧ q ∉ M.out := by
  have h := List.nodup_iff_count.mp hn q
  have hd := List.count_pos_iff.mpr hq
  simp only [MontLayout.wires,List.count_cons,List.count_append] at h
  constructor <;> intro hh <;> have hh' := List.count_pos_iff.mpr hh <;> omega

private theorem work_away (c : Wire) (M : MontLayout) (den : List Wire)
    (hn : (c :: den ++ M.wires).Nodup) (q : Wire) (hq : q ∈ M.work) :
    q ∉ M.y ∧ q ∉ M.out := by
  have h := List.nodup_iff_count.mp hn q
  have hd := List.count_pos_iff.mpr hq
  simp only [MontLayout.wires,List.count_cons,List.count_append] at h
  constructor <;> intro hh <;> have hh' := List.count_pos_iff.mpr hh <;> omega

attribute [local irreducible] run montMulControlledAdd montMulControlledSub swapRegisters

/-- Concrete three-stage quotient core, with the inverse already available. -/
theorem states_factor (c : Wire) (M : MontLayout) (den : List Wire)
    (hn : (c :: den ++ M.wires).Nodup) (hw : M.Widths) (hd : den.length = 257)
    (B : Bool) (X Y I : Fp) (hI : B = true → I = X⁻¹) (hX : B = true → X ≠ 0)
    (s s₁ s₂ s₃ : State) (m₁ m₂ m₃ : List Bool)
    (hb : s.basis c = B) (hx : regValue den s.basis = X.val)
    (hi : regValue M.x s.basis = I.val)
    (hy : regValue M.y s.basis = Y.val) (ht : regValue M.out s.basis = 0)
    (hz : regValue M.work s.basis = 0)
    (h₁ : run (montMulControlledAdd c M p) m₁ s = s₁)
    (h₂ : run (swapRegisters c (M.y.take 256) (M.out.take 256)) m₂ s₁ = s₂)
    (h₃ : run (montMulControlledSub c (denView M den) p) m₃ s₂ = s₃) :
    s₃.phase = s.phase ∧
    regValue M.y s₃.basis = (if B then Y/X else Y).val ∧
    ∀ q, q ∉ M.y → s₃.basis q = s.basis q := by
  letI : Fact p.Prime := ⟨p_prime⟩
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hp : p < 2^256 := by norm_num [p]
  obtain ⟨hn₁,hn₃,hw₃,hn₂⟩ := views c M den hn hw hd
  let Q : Fp := if B then Y/X else Y
  let T : Nat := if B then (Y/X).val else 0
  have hprod : (if B then (0 + (I.val * Y.val) % p) % p else 0) = T := by
    cases B with
    | false => simp [T]
    | true => simp [T,hI rfl,div_eq_mul_inv,mul_comm,ZMod.val_mul]
  have tlt : T < 2^256 := by
    dsimp [T]; split <;> first | exact (Y/X).isLt.trans hp | positivity
  have a := montMulControlledAdd_spec c B M p I.val Y.val 0 hw hn₁ hp
    secp256k1_mod_sixteen I.isLt (Y.isLt.trans hp) p_prime.pos s m₁
    ⟨⟨⟨⟨hb,hi⟩,hy⟩,ht⟩,hz⟩
  rw [h₁,hprod] at a
  obtain ⟨ph₁,⟨⟨⟨⟨bc₁,ix₁⟩,yy₁⟩,tt₁⟩,ww₁⟩⟩ := a
  have f₁ (q : Wire) (hq : q ∉ M.out) : s₁.basis q = s.basis q := by
    have h := montMulControlledAdd_frame c B M p I.val Y.val 0 hw hn₁ hp
      secp256k1_mod_sixteen I.isLt (Y.isLt.trans hp) p_prime.pos s m₁ hb hi hy ht hz q hq
    simpa only [h₁] using h
  have sw := swapLow_correct c M.y M.out 256 Y.val T (by rw [hw.y]) (by rw [hw.out]; omega)
    hn₂ (Y.isLt.trans hp) tlt s₁ m₂ yy₁ tt₁
  rw [h₂,bc₁] at sw
  obtain ⟨ph₂,f₂,yy₂,tt₂⟩ := sw
  have yq : regValue M.y s₂.basis = Q.val := by
    cases B <;> simpa [Q,T] using yy₂
  have tj : regValue M.out s₂.basis = if B then Y.val else 0 := by
    cases B <;> simpa [T] using tt₂
  have awayc : c ∉ M.y ∧ c ∉ M.out := by
    have h := (List.nodup_cons.mp hn₂).1
    exact ⟨fun hh => h (List.mem_append_left _ hh), fun hh => h (List.mem_append_right _ hh)⟩
  have bc₂ : s₂.basis c = B := (f₂ c
    (fun h => awayc.1 ((List.take_sublist 256 M.y).subset h))
    (fun h => awayc.2 ((List.take_sublist 256 M.out).subset h))).trans bc₁
  have dx₂ : regValue den s₂.basis = X.val := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hx
    intro q hq
    have h := den_away c M den hn q hq
    exact (f₂ q (fun h' => h.1 ((List.take_sublist 256 M.y).subset h'))
      (fun h' => h.2 ((List.take_sublist 256 M.out).subset h'))).trans (f₁ q h.2)
  have wz₂ : regValue M.work s₂.basis = 0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) ww₁
    intro q hq
    have h := work_away c M den hn q hq
    exact f₂ q (fun h' => h.1 ((List.take_sublist 256 M.y).subset h'))
      (fun h' => h.2 ((List.take_sublist 256 M.out).subset h'))
  have jlt : (if B then Y.val else 0) < p := by cases B; exact p_prime.pos; exact Y.isLt
  have hzout : (if B then ((if B then Y.val else 0) + p - (X.val * Q.val) % p) % p
      else (if B then Y.val else 0)) = 0 := by
    cases B with
    | false => rfl
    | true =>
      have hv : (X.val * (Y/X).val) % p = Y.val := by
        rw [←ZMod.val_mul, mul_comm, div_mul_cancel₀ Y (hX rfl)]
      simp [Q,hv]
  have a₃ := montMulControlledSub_spec c B (denView M den) p X.val Q.val
    (if B then Y.val else 0) hw₃ hn₃ hp secp256k1_mod_sixteen X.isLt (Q.isLt.trans hp)
    jlt s₂ m₃ ⟨⟨⟨⟨bc₂,dx₂⟩,yq⟩,tj⟩,wz₂⟩
  rw [h₃,hzout] at a₃
  obtain ⟨ph₃,⟨⟨⟨⟨_,_⟩,yy₃⟩,tt₃⟩,_⟩⟩ := a₃
  have f₃ (q : Wire) (hq : q ∉ M.out) : s₃.basis q = s₂.basis q := by
    have h := montMulControlledSub_frame c B (denView M den) p X.val Q.val
      (if B then Y.val else 0) hw₃ hn₃ hp secp256k1_mod_sixteen X.isLt (Q.isLt.trans hp)
      jlt s₂ m₃ bc₂ dx₂ yq tj wz₂ q hq
    simpa only [h₃] using h
  refine ⟨ph₃.trans (ph₂.trans ph₁), yy₃, ?_⟩
  intro q hqy
  by_cases hqt : q ∈ M.out
  · exact (regValue_eq_iff M.out s₃.basis s.basis).mp (tt₃.trans ht.symm) q hqt
  · exact (f₃ q hqt).trans ((f₂ q
      (fun h => hqy ((List.take_sublist 256 M.y).subset h))
      (fun h => hqt ((List.take_sublist 256 M.out).subset h))).trans (f₁ q hqt))

theorem states (c : Wire) (M : MontLayout) (den : List Wire)
    (hn : (c :: den ++ M.wires).Nodup) (hw : M.Widths) (hd : den.length = 257)
    (B : Bool) (X Y : Fp) (hX : B = true → X ≠ 0)
    (s s₁ s₂ s₃ : State) (m₁ m₂ m₃ : List Bool)
    (hb : s.basis c = B) (hx : regValue den s.basis = X.val)
    (hi : regValue M.x s.basis = (if B then X⁻¹ else 0).val)
    (hy : regValue M.y s.basis = Y.val) (ht : regValue M.out s.basis = 0)
    (hz : regValue M.work s.basis = 0)
    (h₁ : run (montMulControlledAdd c M p) m₁ s = s₁)
    (h₂ : run (swapRegisters c (M.y.take 256) (M.out.take 256)) m₂ s₁ = s₂)
    (h₃ : run (montMulControlledSub c (denView M den) p) m₃ s₂ = s₃) :
    s₃.phase = s.phase ∧
    regValue M.y s₃.basis = (if B then Y/X else Y).val ∧
    ∀ q, q ∉ M.y → s₃.basis q = s.basis q := by
  exact states_factor c M den hn hw hd B X Y (if B then X⁻¹ else 0)
    (by intro h; simp [h]) hX s s₁ s₂ s₃ m₁ m₂ m₃ hb hx hi hy ht hz h₁ h₂ h₃

/-- All-tape correctness of the emitted gate list, including every non-numerator
wire and the incoming phase. The temporary quotient is actually cleared. -/
theorem correct (c : Wire) (M : MontLayout) (den : List Wire)
    (hn : (c :: den ++ M.wires).Nodup) (hw : M.Widths) (hd : den.length = 257)
    (B : Bool) (X Y : Fp) (hX : B = true → X ≠ 0) (s : State) (m : List Bool)
    (hb : s.basis c = B) (hx : regValue den s.basis = X.val)
    (hi : regValue M.x s.basis = (if B then X⁻¹ else 0).val)
    (hy : regValue M.y s.basis = Y.val) (ht : regValue M.out s.basis = 0)
    (hz : regValue M.work s.basis = 0) :
    (run (program c M den) m s).phase = s.phase ∧
    regValue M.y (run (program c M den) m s).basis = (if B then Y/X else Y).val ∧
    ∀ q, q ∉ M.y → (run (program c M den) m s).basis q = s.basis q := by
  simp only [program,run_append,run_take]
  exact states c M den hn hw hd B X Y hX s _ _ _ m
    (m.drop (measurementCount (montMulControlledAdd c M p)))
    (m.drop (measurementCount (montMulControlledAdd c M p ++
      swapRegisters c (M.y.take 256) (M.out.take 256)))) hb hx hi hy ht hz rfl rfl rfl

theorem correct_factor (c : Wire) (M : MontLayout) (den : List Wire)
    (hn : (c :: den ++ M.wires).Nodup) (hw : M.Widths) (hd : den.length = 257)
    (B : Bool) (X Y I : Fp) (hI : B = true → I = X⁻¹) (hX : B = true → X ≠ 0) (s : State) (m : List Bool)
    (hb : s.basis c = B) (hx : regValue den s.basis = X.val)
    (hi : regValue M.x s.basis = I.val)
    (hy : regValue M.y s.basis = Y.val) (ht : regValue M.out s.basis = 0)
    (hz : regValue M.work s.basis = 0) :
    (run (program c M den) m s).phase = s.phase ∧
    regValue M.y (run (program c M den) m s).basis = (if B then Y/X else Y).val ∧
    ∀ q, q ∉ M.y → (run (program c M den) m s).basis q = s.basis q := by
  simp only [program,run_append,run_take]
  exact states_factor c M den hn hw hd B X Y I hI hX s _ _ _ m
    (m.drop (measurementCount (montMulControlledAdd c M p)))
    (m.drop (measurementCount (montMulControlledAdd c M p ++
      swapRegisters c (M.y.take 256) (M.out.take 256)))) hb hx hi hy ht hz rfl rfl rfl

theorem counts (c : Wire) (M : MontLayout) (den : List Wire)
    (hn : (c :: den ++ M.wires).Nodup) (hw : M.Widths) (hd : den.length = 257) :
    toffoliCount (program c M den) = toffoliCount (montMulControlledAdd c M p) + 256 +
      toffoliCount (montMulControlledSub c (denView M den) p) ∧
    measurementCount (program c M den) = measurementCount (montMulControlledAdd c M p) +
      measurementCount (montMulControlledSub c (denView M den) p) := by
  have hs := (views c M den hn hw hd).2.2.2
  have nd : (c :: M.y.take 256 ++ M.out.take 256).Nodup :=
    (((List.take_sublist 256 M.y).append (List.take_sublist 256 M.out)).cons₂ c).nodup hs
  have hl : (M.y.take 256).length = (M.out.take 256).length := by simp [hw.y,hw.out]
  have hc := swapRegisters_resources c (M.y.take 256) (M.out.take 256) hl nd
  simp only [program,toffoliCount_append,measurementCount_append,hc.1,hc.2.1,add_zero]
  simp [hw.y]

end ECDSAAdd.Arithmetic.InverseQuotientCore
