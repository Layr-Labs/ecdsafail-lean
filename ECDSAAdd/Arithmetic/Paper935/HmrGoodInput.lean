import ECDSAAdd.Arithmetic.Paper935.HmrRowMulSpec
import ECDSAAdd.Arithmetic.Paper935.FusedFailureEvents

namespace ECDSAAdd.Arithmetic.Paper935

/-- Physical binding at the actual call boundary. Numerical success conditions
are deliberately absent: they will come from the original-label bad set. -/
structure HmrCallBinding (L : HmrRowMulLayout) (call : FusedCall) (s : State) : Prop where
  coefficient : L.row.value s.basis=call.coefficient
  multiplier : regValue L.y s.basis=call.multiplier
  output_zero : ∀q∈L.out,s.basis q=false
  scratch_zero : ∀q∈L.scratch,s.basis q=false

/-- The bad set supplies arithmetic conditions only for enabled modeled calls.
Physical values and clean ancilla are separate, explicit input facts. -/
theorem hmr_pre_of_not_bad {X : Type*} [Fintype X] [DecidableEq X]
    (events : FailureEvents X) (scaling : Finset X) (calls : X → List FusedCall)
    (x : X) (call : FusedCall) (member : call∈calls x) (enabled : call.enabled=true)
    (good : x∉scalingBad events scaling∪(fusedFailures calls).bad)
    (L : HmrRowMulLayout) (s : State) (binding : HmrCallBinding L call s) :
    HmrRowMulPre L call s ∧ call.SignGood := by
  have outside : x∉(fusedFailures calls).bad := fun h => good (Finset.mem_union_right _ h)
  have numerical := (fusedFailures_good calls x).mp outside call member enabled
  refine ⟨?_,numerical.2.2.2⟩
  exact ⟨⟨binding.multiplier,binding.output_zero,binding.scratch_zero,
    numerical.2.1,numerical.1,numerical.2.2.1⟩,binding.coefficient⟩

/-- Consume the good-label bridge at an actual reached state, without resetting
the tape or replacing the physical input by the original encoded label. -/
theorem hmr_reached_call_output {X : Type*} [Fintype X] [DecidableEq X]
    (events : FailureEvents X) (scaling : Finset X) (calls : X → List FusedCall)
    (x : X) (call : FusedCall) (member : call∈calls x) (enabled : call.enabled=true)
    (good : x∉scalingBad events scaling∪(fusedFailures calls).bad)
    (L : HmrRowMulLayout) (P H : RecordedProgram) (forward : HmrRowMulSpec L H)
    (s : State) (tape : List Bool) (cursor : Nat)
    (binding : HmrCallBinding L call (runWithTape P tape cursor s))
    (legal : forward.legalCursor (cursor+recordedMeasurementCount P)) :
    regValue L.out (runWithTape (P++H) tape cursor s).basis=call.beforeSign ∧
    call.SignGood := by
  have pre := hmr_pre_of_not_bad events scaling calls x call member enabled good
    L (runWithTape P tape cursor s) binding
  rw [runWithTape_append]
  exact ⟨(forward.run call _ tape _ legal pre.1).1,pre.2⟩

end ECDSAAdd.Arithmetic.Paper935
