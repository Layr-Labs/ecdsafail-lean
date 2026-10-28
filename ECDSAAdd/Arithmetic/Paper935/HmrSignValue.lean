import ECDSAAdd.Arithmetic.Paper935.HmrSignSourceBinding
import ECDSAAdd.Arithmetic.Paper935.SignPlacedValue

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

theorem s2SignMap_output : signPayload.map s2SignMap=s2HmrSourceOut := by decide +kernel
theorem s6SignMap_output : signPayload.map s6SignMap=s6HmrSourceOut := by decide +kernel
theorem s2SignMap_control : s2SignMap 0=768 := rfl
theorem s6SignMap_control : s6SignMap 0=795 := rfl

attribute [local irreducible] s2SignMap s6SignMap s2SourceSign s6SourceSign
  s2HmrSourceOut s6HmrSourceOut s2HmrSeamPorts s6HmrSeamPorts FusedCall.beforeSign

/-- Actual s2 sign output. Good arithmetic, value encoding, and the negate
control are independent premises supplied at this actual source boundary. -/
theorem s2SourceSign_of_good (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (clean : ∀q∈s2HmrSeamPorts.anc,s.basis q=false)
    (value : regValue s2HmrSourceOut s.basis=call.beforeSign)
    (negate : call.negate=(s.basis 768 ^^ s.basis s2HmrSourceRow.sign))
    (good : call.SignGood) :
    regValue s2HmrSourceOut (runWithTape s2SourceSign tape cursor s).basis=
      if call.negate then fold32Prime-call.beforeSign else call.beforeSign := by
  have ready : ∀i<24,s.basis (s2SignMap (257+i))=false := by
    intro i hi
    apply clean
    rw [←s2SignMap_pool]
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  rw [s2SourceSign_run,←s2SignMap_output]
  exact placedSignFix_of_good s2SignMap s2HmrSourceRow.sign s2SignMap_injective call s
    (tape.drop cursor) ready (by rw [s2SignMap_output]; exact value)
    (by simpa only [s2SignMap_control] using negate) good

/-- Actual s6 sign output, before the deferred record-Z and inverse sign. -/
theorem s6SourceSign_of_good (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (clean : ∀q∈s6HmrSeamPorts.anc,s.basis q=false)
    (value : regValue s6HmrSourceOut s.basis=call.beforeSign)
    (negate : call.negate=(s.basis 795 ^^ s.basis s6HmrSourceRow.sign))
    (good : call.SignGood) :
    regValue s6HmrSourceOut (runWithTape s6SourceSign tape cursor s).basis=
      if call.negate then fold32Prime-call.beforeSign else call.beforeSign := by
  have ready : ∀i<24,s.basis (s6SignMap (257+i))=false := by
    intro i hi
    apply clean
    rw [←s6SignMap_pool]
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  rw [s6SourceSign_run,←s6SignMap_output]
  exact placedSignFix_of_good s6SignMap s6HmrSourceRow.sign s6SignMap_injective call s
    (tape.drop cursor) ready (by rw [s6SignMap_output]; exact value)
    (by simpa only [s6SignMap_control] using negate) good

end ECDSAAdd.Arithmetic.Paper935
