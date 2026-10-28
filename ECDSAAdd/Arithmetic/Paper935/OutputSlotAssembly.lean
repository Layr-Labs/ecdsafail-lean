import ECDSAAdd.Arithmetic.Paper935.OutputSlotOwnership

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

def EndpointOutputCertificate (p ordinal : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (O : Finset Wire) (v : BasisState) (m : List Bool) (s : State) : Prop :=
  runWithTape (endpointSlotProgram p ordinal slots E) m ordinal s=withOutput O v s ∧
  RecordedWellFormedAt ordinal (endpointSlotProgram p ordinal slots E) ∧
  (∀ q∈recordedWires (endpointSlotProgram p ordinal slots E),q<935) ∧
  recordedToffoliCount (endpointSlotProgram p ordinal slots E)=
    recordedToffoliCount (seededAuthorWalkProgram p slots)+recordedToffoliCount E+
    recordedToffoliCount (seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots) ∧
  recordedMeasurementCount (endpointSlotProgram p ordinal slots E)=
    recordedMeasurementCount (seededAuthorWalkProgram p slots)+recordedMeasurementCount E+
    recordedMeasurementCount (seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots) ∧
  O.card≤28 ∧
  (∃ retained : Arena, ∃ temporary : Finset Wire, ∃ during : Arena,
    (authorClosedArena slots).reserve O=some retained ∧
    retained.reserve temporary=some during ∧ recordedWires E⊆during.live ∧
    during.release temporary (endpointAfter p ordinal slots E m s).basis=some retained ∧
    O⊆retained.live ∧ Disjoint O temporary ∧
    retained.Ready (endpointAfter p ordinal slots E m s).basis ∧
    O.card+temporary.card≤315 ∧ during.live.card≤935) ∧
  (∀ q∈arenaWires,q∉seedBefore.live∪O →
    (runWithTape (endpointSlotProgram p ordinal slots E) m ordinal s).basis q=false)

/-- Complete conditional output certificate. There is no instantiated output
placement and no claim of a 256-bit isolated output. E returns temporary work
but transfers the retained output to its eventual consumer. -/
theorem endpointSlot_output_certified {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (coprime : Int.gcd p (input x)=1) (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x) (E : RecordedProgram)
    (O : Finset Wire) (v : BasisState) (contract : EndpointOutputContract p ordinal slots E O v m s) :
    EndpointOutputCertificate p ordinal slots E O v m s := by
  have result := endpointSlot_withOutput input p hp x odd coprime good slots compiled s m ordinal ready encoding E O v contract
  have closed := seededAuthorWalk_closer_release input p hp x odd coprime good slots compiled s m
    (m.drop (endpointCursor p ordinal slots)) ordinal ready encoding
  refine ⟨result,endpointSlot_wellFormed p ordinal slots compiled E contract.wellFormed,
    endpointSlot_address_bound p ordinal slots compiled E contract.arena,
    (endpointSlot_counts p ordinal slots E).1,(endpointSlot_counts p ordinal slots E).2,
    (Finset.card_le_card contract.isolated).trans (retainedOutputSpace_card_le p ordinal slots compiled),
    endpointOutputBorrow_capacity slots compiled O E (endpointClosed p ordinal slots m s) m
      (endpointCursor p ordinal slots) closed.2.1 contract.borrow,?_⟩
  intro q hq hn
  have no : q∉O := fun h => hn (Finset.mem_union_right _ h)
  have ns : q∉seedBefore.live := fun h => hn (Finset.mem_union_left _ h)
  rw [result]
  simpa only [withOutput,if_neg no] using ready q hq ns

/-- Explicit user-facing reading of the state equality: same phase, original
bits off O, and precisely the declared output on O. -/
theorem endpointSlot_output_bits (p ordinal : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (O : Finset Wire) (v : BasisState) (m : List Bool) (s : State)
    (certificate : EndpointOutputCertificate p ordinal slots E O v m s) :
    (runWithTape (endpointSlotProgram p ordinal slots E) m ordinal s).phase=s.phase ∧
    (∀ q∉O,(runWithTape (endpointSlotProgram p ordinal slots E) m ordinal s).basis q=s.basis q) ∧
    (∀ q∈O,(runWithTape (endpointSlotProgram p ordinal slots E) m ordinal s).basis q=v q) := by
  rw [certificate.1]
  exact ⟨rfl,fun q h => if_neg h,fun q h => if_pos h⟩

end ECDSAAdd.Arithmetic.Paper935
