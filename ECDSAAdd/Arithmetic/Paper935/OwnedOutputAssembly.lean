import ECDSAAdd.Arithmetic.Paper935.OwnedOutputOwnership

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

def EndpointOwnedOutputCertificate (p ordinal : Nat) (slots : List HistoricalSlot)
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
  O.card≤256 ∧ O⊆(authorClosedArena slots).live ∧
  (∃ temporary : Finset Wire, ∃ during : Arena,
    temporary⊆arenaWires\(authorClosedArena slots).live ∧
    (authorClosedArena slots).reserve temporary=some during ∧ recordedWires E⊆during.live ∧
    during.release temporary (endpointAfter p ordinal slots E m s).basis=some (authorClosedArena slots) ∧
    Disjoint O temporary ∧ (authorClosedArena slots).Ready (endpointAfter p ordinal slots E m s).basis ∧
    temporary.card≤315 ∧ during.live.card≤935 ∧ during.live.card=620+temporary.card) ∧
  seedBefore.Ready (runWithTape (endpointSlotProgram p ordinal slots E) m ordinal s).basis

/-- Conditional endpoint certificate with a proved 256-bit host placement.
E remains a supplied program with explicit output and cleanup obligations; the
256 output sites are already part of the 620 live sites, not new borrowing. -/
theorem endpointSlot_ownedOutput_certified {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (coprime : Int.gcd p (input x)=1) (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x) (E : RecordedProgram)
    (O : Finset Wire) (v : BasisState) (contract : EndpointOwnedOutputContract p ordinal slots E O v m s) :
    EndpointOwnedOutputCertificate p ordinal slots E O v m s := by
  have result := endpointSlot_withOwnedOutput input p hp x odd coprime good slots compiled s m ordinal ready encoding E O v contract
  have closed := seededAuthorWalk_closer_release input p hp x odd coprime good slots compiled s m
    (m.drop (endpointCursor p ordinal slots)) ordinal ready encoding
  have ownership := endpointOwnedOutputBorrow_capacity slots compiled O contract.host E
    (endpointClosed p ordinal slots m s) m (endpointCursor p ordinal slots) closed.2.1 contract.borrow
  refine ⟨result,endpointSlot_wellFormed p ordinal slots compiled E contract.wellFormed,
    endpointSlot_address_bound p ordinal slots compiled E contract.arena,
    (endpointSlot_counts p ordinal slots E).1,(endpointSlot_counts p ordinal slots E).2,
    ownership.1,ownership.2.1,ownership.2.2,?_⟩
  intro q hq hn
  have no : q∉O := fun h => hn (Finset.mem_union_right _ (contract.host h))
  rw [result]
  simpa only [withOutput,if_neg no] using ready q hq hn

/-- Explicit user-facing reading of the state equality: same phase, original
bits off O, and precisely the declared output on O. -/
theorem endpointSlot_ownedOutput_bits (p ordinal : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (O : Finset Wire) (v : BasisState) (m : List Bool) (s : State)
    (certificate : EndpointOwnedOutputCertificate p ordinal slots E O v m s) :
    (runWithTape (endpointSlotProgram p ordinal slots E) m ordinal s).phase=s.phase ∧
    (∀ q∉O,(runWithTape (endpointSlotProgram p ordinal slots E) m ordinal s).basis q=s.basis q) ∧
    (∀ q∈O,(runWithTape (endpointSlotProgram p ordinal slots E) m ordinal s).basis q=v q) := by
  rw [certificate.1]
  exact ⟨rfl,fun q h => if_neg h,fun q h => if_pos h⟩

end ECDSAAdd.Arithmetic.Paper935
