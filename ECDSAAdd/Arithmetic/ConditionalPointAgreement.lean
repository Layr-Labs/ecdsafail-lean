import ECDSAAdd.Arithmetic.ConditionalPointDialogSpec
import ECDSAAdd.Framework.EncodedBudget
import ECDSAAdd.Arithmetic.RecordedPointDialogSpec

namespace ECDSAAdd.Arithmetic.ConditionalPointDialog
open Secp256k1 FailureBudget FiniteUnitary RecordedQuantum
noncomputable section
local instance : DecidableEq Point := Classical.decEq _

/-- The conditional consumer emits exactly the original program for an exact
provider. Existing exact correctness and resource claims retain their code. -/
theorem program_ofExact (backend : RecordedPointArithmeticBackend)
    (L : ControlledPointLayout) (C : Point) :
    program (.ofExact backend) L C = RecordedPointDialog.program backend L C := by
  cases C <;> rfl

/-- Independent mathematical controlled point translation, with subtraction as
its inverse. This includes infinity and exceptional points. -/
def pointAddPerm (C : Point) : (Bool × Point) ≃ (Bool × Point) where
  toFun x := (x.1, if x.1 then x.2+C else x.2)
  invFun x := (x.1, if x.1 then x.2-C else x.2)
  left_inv x := by rcases x with ⟨b,R⟩; cases b <;> simp
  right_inv x := by rcases x with ⟨b,R⟩; cases b <;> simp

@[simp] theorem pointAddPerm_apply (C : Point) (b : Bool) (R : Point) :
    pointAddPerm C (b,R) = (b, if b then R+C else R) := rfl

private theorem point_bits_eq {r : PointReg} {R : Point} {s t : BasisState}
    (hs : Holds.holds s r R) (ht : Holds.holds t r R)
    (q : Wire) (hq : q ∈ PointAddLayout.pointWires r) : s q = t q := by
  obtain ⟨hf,hx,hy⟩ := (point_holds _ _ _).mp hs
  obtain ⟨hf',hx',hy'⟩ := (point_holds _ _ _).mp ht
  simp only [PointAddLayout.pointWires, List.mem_append, List.mem_cons] at hq
  rcases hq with (rfl | hq) | hq
  · exact hf.trans hf'.symm
  · exact (regValue_eq_iff _ _ _).mp (hx.trans hx'.symm) q hq
  · exact (regValue_eq_iff _ _ _).mp (hy.trans hy'.symm) q hq

/-- Lift the proved point-add pipeline to full-state, all-phase/all-tape
agreement. The exceptional set is on ORIGINAL inputs; both arithmetic calls
must be safe there, with their different actual mathematical operands. -/
theorem recorded_agreement {X : Type*} [Fintype X] [DecidableEq X]
    (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    (input output : X → BasisState) (control : X → Bool) (point : X → Point)
    (bad : Finset X)
    (hi : ∀ x, PointDialogBoundary L (point x) (control x) (fun _ => false) (input x))
    (ho : ∀ x, Holds.holds (output x) L.point (if control x then point x+C else point x))
    (frame : ∀ x q, q ∉ PointAddLayout.pointWires L.point → output x q = input x q)
    (hsafe : ∀ x, x ∉ bad → Safe backend (control x) (point x) C) :
    RecordedAgreement (program backend L C) input output bad := by
  intro x hx phase tape
  have hsafe' := hsafe x hx
  obtain ⟨hp,hout⟩ := add_boundary backend L hw hn (control x) (point x) C hsafe'
    ⟨phase,input x⟩ tape (hi x)
  have hb : (runWithTape (program backend L C) tape 0 ⟨phase,input x⟩).basis = output x := by
    funext q
    by_cases hq : q ∈ PointAddLayout.pointWires L.point
    · exact point_bits_eq hout.point (ho x) q hq
    · exact (add_frame backend L hw hn (control x) (point x) C hsafe'
        ⟨phase,input x⟩ tape (hi x) q hq).trans (frame x q hq).symm
  cases he : runWithTape (program backend L C) tape 0 ⟨phase,input x⟩ with
  | mk ph bs => simp only [he] at hp hb; cases hp; cases hb; rfl

/-- Consumer-side end-to-end quantum theorem for an encoded controlled point
addition. The provider is conditional, not required correct on failed inputs.
The circuit must realize this very program, not an unrelated implementation. -/
theorem pointAdd_budget [Fintype (Bool × Point)]
    (backend : ConditionalPointArithmeticBackend) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    {n l : Nat} (c : Circuit n 0 l) (hc : c.program = program backend L C)
    (ι : (Bool × Point) ↪ Bits n) (μ : InputLaw (Bool × Point))
    (bad : Finset (Bool × Point)) (ε : ℝ) (he : 0 ≤ ε) (hlt : ε < 1)
    (hm : μ.mass bad ≤ ε)
    (hi : ∀ x, PointDialogBoundary L x.2 x.1 (fun _ => false) (extend (ι x)))
    (frame : ∀ x q, q ∉ PointAddLayout.pointWires L.point →
      extend (ι (pointAddPerm C x)) q = extend (ι x) q)
    (hsafe : ∀ x, x ∉ bad → Safe backend x.1 x.2 C) :
    QuantumBudget (actual c).toContinuousLinearMap
      (ideal l (encodedPerm ι (pointAddPerm C))).toContinuousLinearMap
      (μ.push ι) (encodedBad ι bad) ε := by
  apply budget_of_encoded c ι (pointAddPerm C) μ bad ε he hlt hm
  rw [hc]
  apply recorded_agreement backend L hw hn C _ _ Prod.fst Prod.snd bad hi _ frame hsafe
  intro x
  exact (hi (pointAddPerm C x)).point

end
end ECDSAAdd.Arithmetic.ConditionalPointDialog
