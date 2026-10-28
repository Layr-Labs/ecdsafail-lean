import ECDSAAdd.Arithmetic.InversePointBackend
import ECDSAAdd.Arithmetic.PointInputEncoding
import ECDSAAdd.Arithmetic.Paper935.FailureAssembly

namespace ECDSAAdd.Arithmetic.PointInverseEndpoint
open Secp256k1 FailureBudget
noncomputable section
local instance : DecidableEq Point := Classical.decEq _
local instance : NeZero p := ⟨p_prime.ne_zero⟩

/-- The actual inverse input of controlled point addition. `none` means that
adding infinity emits no program. Disabled calls retain their actual X value. -/
def callInput (C : Point) (x : Bool × Point) : Option (Fp × Bool) :=
  match C with
  | .zero => none
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx _cy hc =>
    let X := ((coordinates x.2).getD (0,0)).1
    if dialogOrdinary x.1 x.2 (.some hc) then some (X-cx,true) else some (X,false)

/-- The actual enabled inverse call never has a zero denominator, including
all exceptional point-add branches. -/
theorem callInput_nonzero (C : Point) (x : Bool × Point) (X : Fp)
    (h : callInput C x = some (X,true)) : X ≠ 0 := by
  cases C with
  | zero => simp [callInput] at h
  | @some cx cy hc =>
    have hC : (WeierstrassCurve.Affine.Point.some hc : Point) ≠ 0 := by
      simp
    simp only [callInput] at h
    split at h
    next hg =>
      have he := ((dialogOrdinary_true x.1 x.2 (.some hc) hC).mp hg).2
      cases hr : x.2 with
      | zero => exact False.elim (he.1 hr)
      | @some xx yy hR =>
        rw [hr] at he h
        have hd := (dialog_denominators_ne_zero hR hc he.2.1 he.2.2.1 he.2.2.2).1
        have hv : xx-cx = X := by simpa [coordinates] using congrArg (fun z => z.map Prod.fst) h
        rw [←hv]
        exact sub_ne_zero.mpr hd
    next hg => simp at h

def callSafe (ep : PointInverseEndpoint) : Option (Fp × Bool) → Prop
  | none => True
  | some (X,b) => ep.safe X b

theorem safe_iff (ep : PointInverseEndpoint) (C : Point) (x : Bool × Point) :
    ConditionalPointDialog.Safe ep.backend x.1 x.2 C ↔ ep.callSafe (callInput C x) := by
  cases C with
  | zero => rfl
  | some hc =>
    simp only [ConditionalPointDialog.Safe,ConditionalPointDialog.GenericSafe,
      backend,callInput,callSafe,Bool.false_eq_true,if_false,ite_true]
    split <;> simp

/-- Bad inputs under the *induced* inverse law, not an assumed uniform law. -/
def callBad (ep : PointInverseEndpoint) : Finset (Option (Fp × Bool)) := by
  classical
  exact Finset.univ.filter (fun z => ¬ ep.callSafe z)

def pointBad [Fintype (Bool × Point)] (ep : PointInverseEndpoint) (C : Point) :
    Finset (Bool × Point) := Finset.univ.filter (fun x => callInput C x ∈ ep.callBad)

theorem safe_outside [Fintype (Bool × Point)] (ep : PointInverseEndpoint) (C : Point)
    (x : Bool × Point) (hx : x ∉ ep.pointBad C) :
    ConditionalPointDialog.Safe ep.backend x.1 x.2 C := by
  rw [safe_iff]
  simpa [pointBad,callBad] using hx

theorem bad_mass [Fintype (Bool × Point)] (ep : PointInverseEndpoint) (C : Point)
    (μ : InputLaw (Bool × Point)) :
    μ.mass (ep.pointBad C) = (μ.push (callInput C)).mass ep.callBad := by
  rw [InputLaw.push_mass]; rfl

/-- Zero denominators have exactly zero mass among enabled inverse calls; they
do not consume any of the numerical failure budget. -/
theorem enabled_zero_mass [Fintype (Bool × Point)] (C : Point)
    (μ : InputLaw (Bool × Point)) :
    (μ.push (callInput C)).mass {some ((0 : Fp),true)} = 0 := by
  rw [InputLaw.push_mass]
  have hempty : Finset.univ.filter (fun x => callInput C x ∈ ({some ((0 : Fp),true)} : Finset _)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have he : callInput C x = some ((0 : Fp),true) := by simpa using (Finset.mem_filter.mp hx).2
    exact callInput_nonzero C x 0 he rfl
  rw [hempty]
  simp [InputLaw.mass]

/-- The inverse failure bound is measured under the denominator/control law
induced by the original point input distribution. No uniformity is assumed. -/
theorem budget [Fintype (Bool × Point)]
    (ep : PointInverseEndpoint) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    {n l : Nat} (c : RecordedQuantum.Circuit n 0 l)
    (hc : c.program = ConditionalPointDialog.program ep.backend L C)
    (hb : PointInputEncoding.Bounded L n) (μ : InputLaw (Bool × Point))
    (ε : ℝ) (he : 0 ≤ ε) (hlt : ε < 1)
    (hm : (μ.push (callInput C)).mass ep.callBad ≤ ε) :
    QuantumBudget (RecordedQuantum.actual c).toContinuousLinearMap
      (RecordedQuantum.ideal l (encodedPerm (PointInputEncoding.encoding L hw hn hb)
        (ConditionalPointDialog.pointAddPerm C))).toContinuousLinearMap
      (μ.push (PointInputEncoding.encoding L hw hn hb))
      (encodedBad (PointInputEncoding.encoding L hw hn hb) (ep.pointBad C)) ε := by
  apply PointInputEncoding.budget ep.backend L hw hn C c hc hb μ (ep.pointBad C) ε he hlt
  · rw [ep.bad_mass C μ]; exact hm
  · exact ep.safe_outside C

/-- Four inverse failure categories give a point-add budget under the exact
induced call distribution. Coverage is explicit; no independence is required. -/
theorem budget_of_events [Fintype (Bool × Point)]
    (ep : PointInverseEndpoint) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    {n l : Nat} (c : RecordedQuantum.Circuit n 0 l)
    (hc : c.program = ConditionalPointDialog.program ep.backend L C)
    (hb : PointInputEncoding.Bounded L n) (μ : InputLaw (Bool × Point))
    (events : Paper935.FailureEvents (Option (Fp × Bool)))
    (bounds : Paper935.FailureBounds (μ.push (callInput C)) events)
    (cover : ep.callBad ⊆ events.bad) (hlt : bounds.total < 1) :
    QuantumBudget (RecordedQuantum.actual c).toContinuousLinearMap
      (RecordedQuantum.ideal l (encodedPerm (PointInputEncoding.encoding L hw hn hb)
        (ConditionalPointDialog.pointAddPerm C))).toContinuousLinearMap
      (μ.push (PointInputEncoding.encoding L hw hn hb))
      (encodedBad (PointInputEncoding.encoding L hw hn hb) (ep.pointBad C)) bounds.total := by
  apply ep.budget L hw hn C c hc hb μ bounds.total bounds.total_nonneg hlt
  exact ((μ.push (callInput C)).mass_mono cover).trans bounds.mass_le

end
end ECDSAAdd.Arithmetic.PointInverseEndpoint
