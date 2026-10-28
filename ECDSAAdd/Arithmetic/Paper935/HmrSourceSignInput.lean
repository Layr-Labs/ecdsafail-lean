import ECDSAAdd.Arithmetic.Paper935.HmrSignValue
import ECDSAAdd.Arithmetic.Paper935.HmrGoodInput

namespace ECDSAAdd.Arithmetic.Paper935
attribute [local irreducible] s2SourceSign s6SourceSign s2HmrSourceRow s6HmrSourceRow
  s2HmrSeamPorts s6HmrSeamPorts s2HmrSourceOut s6HmrSourceOut FusedCall.beforeSign

/-- Original-label good input and the reached physical binding supply the
arithmetic conditions; forward execution supplies the value and clean pool.
The negate binding is still checked at the actual post-forward state. -/
theorem s2SourceSign_reached_of_not_bad {X : Type*} [Fintype X] [DecidableEq X]
    (events : FailureEvents X) (scaling : Finset X) (calls : X → List FusedCall)
    (x : X) (call : FusedCall) (member : call∈calls x) (enabled : call.enabled=true)
    (good : x∉scalingBad events scaling∪(fusedFailures calls).bad)
    (P H : RecordedProgram) (forward : HmrRowMulSpec s2HmrSourceLayout H)
    (s : State) (tape : List Bool) (cursor : Nat)
    (binding : HmrCallBinding s2HmrSourceLayout call (runWithTape P tape cursor s))
    (legal : forward.legalCursor (cursor+recordedMeasurementCount P))
    (negate : call.negate =
      ((runWithTape (P++H) tape cursor s).basis 768 ^^
       (runWithTape (P++H) tape cursor s).basis s2HmrSourceRow.sign)) :
    regValue s2HmrSourceOut (runWithTape (P++H++s2SourceSign) tape cursor s).basis =
      if call.negate then fold32Prime-call.beforeSign else call.beforeSign := by
  have pre := hmr_pre_of_not_bad events scaling calls x call member enabled good
    s2HmrSourceLayout (runWithTape P tape cursor s) binding
  have h := forward.run call (runWithTape P tape cursor s) tape
    (cursor+recordedMeasurementCount P) legal pre.1
  have clean : ∀q∈s2HmrSeamPorts.anc,(runWithTape (P++H) tape cursor s).basis q=false := by
    intro q hq
    rw [runWithTape_append]
    exact h.2.2.2.2.1 q (Finset.mem_union_left _ (List.mem_toFinset.mpr hq))
  have value : regValue s2HmrSourceOut (runWithTape (P++H) tape cursor s).basis=call.beforeSign := by
    rw [runWithTape_append]
    exact h.1
  rw [runWithTape_append]
  exact s2SourceSign_of_good call _ tape _ clean value negate pre.2

/-- Original-label good input and the reached physical binding supply the
arithmetic conditions; forward execution supplies the value and clean pool.
The negate binding is still checked at the actual post-forward state. -/
theorem s6SourceSign_reached_of_not_bad {X : Type*} [Fintype X] [DecidableEq X]
    (events : FailureEvents X) (scaling : Finset X) (calls : X → List FusedCall)
    (x : X) (call : FusedCall) (member : call∈calls x) (enabled : call.enabled=true)
    (good : x∉scalingBad events scaling∪(fusedFailures calls).bad)
    (P H : RecordedProgram) (forward : HmrRowMulSpec s6HmrSourceLayout H)
    (s : State) (tape : List Bool) (cursor : Nat)
    (binding : HmrCallBinding s6HmrSourceLayout call (runWithTape P tape cursor s))
    (legal : forward.legalCursor (cursor+recordedMeasurementCount P))
    (negate : call.negate =
      ((runWithTape (P++H) tape cursor s).basis 795 ^^
       (runWithTape (P++H) tape cursor s).basis s6HmrSourceRow.sign)) :
    regValue s6HmrSourceOut (runWithTape (P++H++s6SourceSign) tape cursor s).basis =
      if call.negate then fold32Prime-call.beforeSign else call.beforeSign := by
  have pre := hmr_pre_of_not_bad events scaling calls x call member enabled good
    s6HmrSourceLayout (runWithTape P tape cursor s) binding
  have h := forward.run call (runWithTape P tape cursor s) tape
    (cursor+recordedMeasurementCount P) legal pre.1
  have clean : ∀q∈s6HmrSeamPorts.anc,(runWithTape (P++H) tape cursor s).basis q=false := by
    intro q hq
    rw [runWithTape_append]
    exact h.2.2.2.2.1 q (Finset.mem_union_left _ (List.mem_toFinset.mpr hq))
  have value : regValue s6HmrSourceOut (runWithTape (P++H) tape cursor s).basis=call.beforeSign := by
    rw [runWithTape_append]
    exact h.1
  rw [runWithTape_append]
  exact s6SourceSign_of_good call _ tape _ clean value negate pre.2

end ECDSAAdd.Arithmetic.Paper935
