import ECDSAAdd.Arithmetic.ConditionalPointPhysical
import ECDSAAdd.Arithmetic.InverseBothPhysical
import ECDSAAdd.Arithmetic.InverseBothFailure

namespace ECDSAAdd.Arithmetic.PointInverseEndpoint
open RecordedQuantum Secp256k1 FailureBudget ControlledPointLayout
noncomputable section
local instance : DecidableEq Point := Classical.decEq _

/-- Full implementation bounds imply the input-register bounds used by the
clean-state encoding. -/
theorem inputBounded_of_used (L : ControlledPointLayout) (n : Nat)
    (hb : L.dialogUsedWires.toFinset ⊆ Finset.range n) : PointInputEncoding.Bounded L n := by
  intro q hq
  apply Finset.mem_range.mp
  apply hb
  simp only [List.mem_toFinset,dialogUsedWires,List.mem_append] at hq ⊢
  tauto

/-- Construct the complete point-add circuit from the actual inverse endpoint.
Physical validity of all fixed point stages and both adapters is discharged. -/
theorem point_realize (ep : PointInverseEndpoint) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    (hp : PhysicalProgram (ep.program L)) (n : Nat)
    (hb : L.dialogUsedWires.toFinset ⊆ Finset.range n) :
    ∃ l, ∃ c : Circuit n 0 l, c.program = ConditionalPointDialog.program ep.bothBackend L C :=
  ConditionalPointDialog.realize ep.bothBackend L hw hn C
    (ep.both_physical L hw hn hp) n hb

/-- End-to-end conditional quantum budget for the constructed point program.
The inverse endpoint and its two induced-input failure bounds remain explicit;
there is no external assumption that the whole point program is a circuit. -/
theorem point_budget [Fintype (Bool × Point)]
    (ep : PointInverseEndpoint) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (C : Point)
    (hp : PhysicalProgram (ep.program L)) (n : Nat)
    (hb : L.dialogUsedWires.toFinset ⊆ Finset.range n) (μ : InputLaw (Bool × Point))
    (ε₁ ε₂ : ℝ) (he₁ : 0 ≤ ε₁) (he₂ : 0 ≤ ε₂) (hlt : ε₁ + ε₂ < 1)
    (hm₁ : (μ.push (callInput C)).mass ep.callBad ≤ ε₁)
    (hm₂ : (μ.push (productCallInput C)).mass ep.callBad ≤ ε₂) :
    ∃ l, ∃ c : Circuit n 0 l,
      c.program = ConditionalPointDialog.program ep.bothBackend L C ∧
      QuantumBudget (actual c).toContinuousLinearMap
        (ideal l (encodedPerm (PointInputEncoding.encoding L hw hn (inputBounded_of_used L n hb))
          (ConditionalPointDialog.pointAddPerm C))).toContinuousLinearMap
        (μ.push (PointInputEncoding.encoding L hw hn (inputBounded_of_used L n hb)))
        (encodedBad (PointInputEncoding.encoding L hw hn (inputBounded_of_used L n hb))
          (ep.twoCallsBad C)) (ε₁ + ε₂) := by
  obtain ⟨l,c,hc⟩ := ep.point_realize L hw hn C hp n hb
  refine ⟨l,c,hc,?_⟩
  exact ep.twoCalls_budget ep.bothBackend (fun _ _ _ _ => Iff.rfl) L hw hn C c hc
    (inputBounded_of_used L n hb) μ ε₁ ε₂ he₁ he₂ hlt hm₁ hm₂

end
end ECDSAAdd.Arithmetic.PointInverseEndpoint
