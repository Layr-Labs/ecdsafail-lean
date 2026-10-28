import ECDSAAdd.Arithmetic.Paper935.EndpointSlotResources

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

def endpointClosed (p ordinal : Nat) (slots : List HistoricalSlot) (m : List Bool) (s : State) : State :=
  run (closerProgram (walkExitBank walkSeedBank slots) p) (m.drop (endpointCursor p ordinal slots))
    (runWithTape (seededAuthorWalkProgram p slots) m ordinal s)

def endpointAfter (p ordinal : Nat) (slots : List HistoricalSlot) (E : RecordedProgram)
    (m : List Bool) (s : State) : State :=
  runWithTape E m (endpointCursor p ordinal slots) (endpointClosed p ordinal slots m s)

/-- A single certificate for the recorded splice, its actual endpoint boundary
and its allocator transaction. It is conditional on E, not an implementation. -/
def EndpointSlotCertificate (p ordinal : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (m : List Bool) (s : State) : Prop :=
  runWithTape (endpointSlotProgram p ordinal slots E) m ordinal s=s ∧
  RecordedWellFormedAt ordinal (endpointSlotProgram p ordinal slots E) ∧
  (∀ q∈recordedWires (endpointSlotProgram p ordinal slots E),q<935) ∧
  recordedToffoliCount (endpointSlotProgram p ordinal slots E)=
    recordedToffoliCount (seededAuthorWalkProgram p slots)+recordedToffoliCount E+
    recordedToffoliCount (seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots) ∧
  recordedMeasurementCount (endpointSlotProgram p ordinal slots E)=
    recordedMeasurementCount (seededAuthorWalkProgram p slots)+recordedMeasurementCount E+
    recordedMeasurementCount (seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots) ∧
  (walkExitArena walkSeedArena slots).release (closerPayloads (walkExitBank walkSeedBank slots)).toFinset
    (endpointClosed p ordinal slots m s).basis=some (authorClosedArena slots) ∧
  (authorClosedArena slots).Ready (endpointClosed p ordinal slots m s).basis ∧
 (∃ qs : Finset Wire, ∃ during : Arena,
    qs⊆arenaWires\(authorClosedArena slots).live ∧
    (authorClosedArena slots).reserve qs=some during ∧
    recordedWires E⊆during.live ∧
    during.release qs (endpointAfter p ordinal slots E m s).basis=some (authorClosedArena slots) ∧
    qs.card≤315 ∧ during.live.card≤935) ∧
  (authorClosedArena slots).Ready (endpointAfter p ordinal slots E m s).basis ∧
  (authorClosedArena slots).reserve (closerPayloads (walkExitBank walkSeedBank slots)).toFinset=
    some (walkExitArena walkSeedArena slots)

/-- Parameterized endpoint slot, including exact State recovery, cursor-safe
records, the physical address bound, costs, and free-only paired borrowing.
Prime/nonzero facts are deliberately not substituted for coprimality here. -/
theorem endpointSlot_certified {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (coprime : Int.gcd p (input x)=1) (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x) (E : RecordedProgram)
    (contract : EndpointContract p ordinal slots E m
      (runWithTape (seededAuthorWalkProgram p slots) m ordinal s)) :
    EndpointSlotCertificate p ordinal slots E m s := by
  have endpoint := seededAuthorWalk_closer_endpoint input p hp x odd coprime good slots compiled s m ordinal ready encoding
  have executed := seededAuthorWalk_run input p hp x odd good slots compiled s m ordinal ready encoding
  have widths := compileAuthorWalk_exit_widths slots compiled
  have positive : 0<p := by
    by_contra bad
    have zero : p=0 := by omega
    simp [zero] at odd
  have fw : 1<2^(walkExitBank walkSeedBank slots).f.payload.length := by rw [widths.1]; decide
  have pw : p<2^(walkExitBank walkSeedBank slots).gv.payload.length := by
    rw [widths.2.2.2]
    exact lt_trans hp (Nat.pow_lt_pow_right (by decide) (by decide))
  have boundary := closerProgram_reclaim_unclose (walkExitBank walkSeedBank slots) p
    (walkExitArena walkSeedArena slots) (compileAuthorWalk_exit_owned slots compiled)
    fw positive pw _ _ [] executed.2.1 endpoint.1 endpoint.2.1 endpoint.2.2 contract.restored
  have closed := seededAuthorWalk_closer_release input p hp x odd coprime good slots compiled s m
    (m.drop (endpointCursor p ordinal slots)) ordinal ready encoding
  exact ⟨endpointSlot_roundtrip input p hp x odd coprime good slots compiled s m ordinal ready encoding E contract,
    endpointSlot_wellFormed p ordinal slots compiled E contract.wellFormed,
    endpointSlot_address_bound p ordinal slots compiled E contract.arena,
    (endpointSlot_counts p ordinal slots E).1,(endpointSlot_counts p ordinal slots E).2,closed.1,closed.2.1,
    endpointBorrow_bounds slots compiled E _ contract.borrow,boundary.1,boundary.2.1⟩

end ECDSAAdd.Arithmetic.Paper935
