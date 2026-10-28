import ECDSAAdd.Arithmetic.InversePointFailure
import ECDSAAdd.Arithmetic.InverseBothBackend

namespace ECDSAAdd.Arithmetic.PointInverseEndpoint
open Secp256k1 FailureBudget
noncomputable section
local instance : DecidableEq Point := Classical.decEq _
local instance : NeZero p := ⟨p_prime.ne_zero⟩

/-- Inverse input used by an inverse-based multiplication arm. -/
def productCallInput (C : Point) (x : Bool × Point) : Option (Fp × Bool) :=
  match C with
  | .zero => none
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
    let X := ((coordinates x.2).getD (0,0)).1
    let Y := ((coordinates x.2).getD (0,0)).2
    if dialogOrdinary x.1 x.2 (.some hc) then some (cx-genericX X Y cx cy,true)
    else some (X,false)

theorem productCallInput_nonzero (C : Point) (x : Bool × Point) (X : Fp)
    (h : productCallInput C x = some (X,true)) : X ≠ 0 := by
  cases C with
  | zero => simp [productCallInput] at h
  | @some cx cy hc =>
    have hC : (WeierstrassCurve.Affine.Point.some hc : Point) ≠ 0 := by simp
    simp only [productCallInput] at h
    split at h
    next hg =>
      have he := ((dialogOrdinary_true x.1 x.2 (.some hc) hC).mp hg).2
      cases hr : x.2 with
      | zero => exact False.elim (he.1 hr)
      | @some xx yy hR =>
        rw [hr] at he h
        have hd := (dialog_denominators_ne_zero hR hc he.2.1 he.2.2.1 he.2.2.2).2
        have hv : cx-genericX xx yy cx cy = X := by
          simpa [coordinates] using congrArg (fun z => z.map Prod.fst) h
        exact hv ▸ hd
    next hg => simp at h

theorem product_enabled_zero_mass [Fintype (Bool × Point)] (C : Point)
    (μ : InputLaw (Bool × Point)) :
    (μ.push (productCallInput C)).mass {some ((0 : Fp),true)} = 0 := by
  rw [InputLaw.push_mass]
  have hempty : Finset.univ.filter
      (fun x => productCallInput C x ∈ ({some ((0 : Fp),true)} : Finset _)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have he : productCallInput C x = some ((0 : Fp),true) := by
      simpa using (Finset.mem_filter.mp hx).2
    exact productCallInput_nonzero C x 0 he rfl
  rw [hempty]
  simp [InputLaw.mass]

theorem twoCalls_safe_iff (ep : PointInverseEndpoint) (backend : ConditionalPointArithmeticBackend)
    (hs : ∀ mul X Y b, backend.safe mul X Y b ↔ ep.safe X b) (C : Point) (x : Bool × Point) :
    ConditionalPointDialog.Safe backend x.1 x.2 C ↔
      ep.callSafe (callInput C x) ∧ ep.callSafe (productCallInput C x) := by
  cases C with
  | zero => simp [ConditionalPointDialog.Safe,callInput,productCallInput,callSafe]
  | some hc =>
    simp only [ConditionalPointDialog.Safe,ConditionalPointDialog.GenericSafe,callInput,productCallInput]
    split <;> simp_all [callSafe]

def productPointBad [Fintype (Bool × Point)] (ep : PointInverseEndpoint) (C : Point) :
    Finset (Bool × Point) := Finset.univ.filter (fun x => productCallInput C x ∈ ep.callBad)

def twoCallsBad [Fintype (Bool × Point)] (ep : PointInverseEndpoint) (C : Point) :
    Finset (Bool × Point) := ep.pointBad C ∪ ep.productPointBad C

theorem twoCalls_safe_outside [Fintype (Bool × Point)] (ep : PointInverseEndpoint)
    (backend : ConditionalPointArithmeticBackend)
    (hs : ∀ mul X Y b, backend.safe mul X Y b ↔ ep.safe X b)
    (C : Point) (x : Bool × Point) (hx : x ∉ ep.twoCallsBad C) :
    ConditionalPointDialog.Safe backend x.1 x.2 C := by
  rw [twoCalls_safe_iff ep backend hs]
  simpa [twoCallsBad,pointBad,productPointBad,callBad] using hx

theorem twoCalls_mass_le [Fintype (Bool × Point)] (ep : PointInverseEndpoint)
    (C : Point) (μ : InputLaw (Bool × Point)) :
    μ.mass (ep.twoCallsBad C) ≤ (μ.push (callInput C)).mass ep.callBad +
      (μ.push (productCallInput C)).mass ep.callBad := by
  rw [InputLaw.push_mass,InputLaw.push_mass]
  exact μ.mass_union_le _ _

/-- Both call laws are induced from the same original input; no independence is needed. -/
theorem twoCalls_budget [Fintype (Bool × Point)]
    (ep : PointInverseEndpoint) (backend : ConditionalPointArithmeticBackend)
    (hs : ∀ mul X Y b, backend.safe mul X Y b ↔ ep.safe X b)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    {n l : Nat} (c : RecordedQuantum.Circuit n 0 l)
    (hc : c.program = ConditionalPointDialog.program backend L C)
    (hb : PointInputEncoding.Bounded L n) (μ : InputLaw (Bool × Point))
    (ε₁ ε₂ : ℝ) (he₁ : 0 ≤ ε₁) (he₂ : 0 ≤ ε₂) (hlt : ε₁ + ε₂ < 1)
    (hm₁ : (μ.push (callInput C)).mass ep.callBad ≤ ε₁)
    (hm₂ : (μ.push (productCallInput C)).mass ep.callBad ≤ ε₂) :
    QuantumBudget (RecordedQuantum.actual c).toContinuousLinearMap
      (RecordedQuantum.ideal l (encodedPerm (PointInputEncoding.encoding L hw hn hb)
        (ConditionalPointDialog.pointAddPerm C))).toContinuousLinearMap
      (μ.push (PointInputEncoding.encoding L hw hn hb))
      (encodedBad (PointInputEncoding.encoding L hw hn hb) (ep.twoCallsBad C)) (ε₁ + ε₂) := by
  apply PointInputEncoding.budget backend L hw hn C c hc hb μ (ep.twoCallsBad C)
    (ε₁ + ε₂) (add_nonneg he₁ he₂) hlt
  · exact (ep.twoCalls_mass_le C μ).trans (add_le_add hm₁ hm₂)
  · exact ep.twoCalls_safe_outside backend hs C

theorem twoCalls_budget_of_events [Fintype (Bool × Point)]
    (ep : PointInverseEndpoint) (backend : ConditionalPointArithmeticBackend)
    (hs : ∀ mul X Y b, backend.safe mul X Y b ↔ ep.safe X b)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    {n l : Nat} (c : RecordedQuantum.Circuit n 0 l)
    (hc : c.program = ConditionalPointDialog.program backend L C)
    (hb : PointInputEncoding.Bounded L n) (μ : InputLaw (Bool × Point))
    (events₁ events₂ : Paper935.FailureEvents (Option (Fp × Bool)))
    (bounds₁ : Paper935.FailureBounds (μ.push (callInput C)) events₁)
    (bounds₂ : Paper935.FailureBounds (μ.push (productCallInput C)) events₂)
    (cover₁ : ep.callBad ⊆ events₁.bad) (cover₂ : ep.callBad ⊆ events₂.bad)
    (hlt : bounds₁.total + bounds₂.total < 1) :
    QuantumBudget (RecordedQuantum.actual c).toContinuousLinearMap
      (RecordedQuantum.ideal l (encodedPerm (PointInputEncoding.encoding L hw hn hb)
        (ConditionalPointDialog.pointAddPerm C))).toContinuousLinearMap
      (μ.push (PointInputEncoding.encoding L hw hn hb))
      (encodedBad (PointInputEncoding.encoding L hw hn hb) (ep.twoCallsBad C))
      (bounds₁.total + bounds₂.total) := by
  apply ep.twoCalls_budget backend hs L hw hn C c hc hb μ _ _
    bounds₁.total_nonneg bounds₂.total_nonneg hlt
  · exact ((μ.push (callInput C)).mass_mono cover₁).trans bounds₁.mass_le
  · exact ((μ.push (productCallInput C)).mass_mono cover₂).trans bounds₂.mass_le

end
end ECDSAAdd.Arithmetic.PointInverseEndpoint
