import ECDSAAdd.Arithmetic.Paper935.CloserWalk
import ECDSAAdd.Arithmetic.Paper935.CloserResources
import ECDSAAdd.Arithmetic.Paper935.UncloserContract
import ECDSAAdd.Arithmetic.Paper935.SeededDecoderUndo

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

/-- The endpoint begins after all forward measurements. Original saved record
indices remain absolute when the reverse subsequently consumes fresh records. -/
def endpointCursor (p ordinal : Nat) (slots : List HistoricalSlot) : Nat :=
  ordinal+recordedMeasurementCount (seededAuthorWalkProgram p slots)

def endpointSlotProgram (p ordinal : Nat) (slots : List HistoricalSlot) (E : RecordedProgram) : RecordedProgram :=
  seededAuthorWalkProgram p slots ++
    embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p) ++ E ++
    embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p).reverse ++
    seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots

/-- An actual allocator transaction supplied by E's caller. The borrowed set
is free in the closed arena; support is owned during execution and release
checks the actual final basis. Temporary nested allocations must be certified
by the caller inside this transaction. -/
def EndpointBorrow (A : Arena) (E : RecordedProgram) (out : State) : Prop :=
  ∃ borrowed : Finset Wire, ∃ during : Arena,
    borrowed⊆arenaWires\A.live ∧ A.reserve borrowed=some during ∧
    recordedWires E⊆during.live ∧ during.release borrowed out.basis=some A

/-- Pointwise contract at the actual closer output and absolute record cursor.
No endpoint implementation or host choice is hidden in this interface. -/
structure EndpointContract (p ordinal : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (m : List Bool) (before : State) : Prop where
  wellFormed : RecordedWellFormedAt (endpointCursor p ordinal slots) E
  arena : recordedWires E⊆arenaWires
  restored : UncloserReady (walkExitBank walkSeedBank slots) before
    (runWithTape E m (endpointCursor p ordinal slots)
      (run (closerProgram (walkExitBank walkSeedBank slots) p) (m.drop (endpointCursor p ordinal slots)) before))
  borrow : EndpointBorrow (authorClosedArena slots) E
    (runWithTape E m (endpointCursor p ordinal slots)
      (run (closerProgram (walkExitBank walkSeedBank slots) p) (m.drop (endpointCursor p ordinal slots)) before))

attribute [local irreducible] seededAuthorWalkProgram seededAuthorWalkReverse closerProgram actualHistoryDecoder

private theorem splice_counts (W R E : RecordedProgram) (C : Program)
    (ht : toffoliCount C=0) (hm : measurementCount C=0) :
    recordedToffoliCount (W++embedRecorded C++E++embedRecorded C.reverse++R)=
      recordedToffoliCount W+recordedToffoliCount E+recordedToffoliCount R ∧
    recordedMeasurementCount (W++embedRecorded C++E++embedRecorded C.reverse++R)=
      recordedMeasurementCount W+recordedMeasurementCount E+recordedMeasurementCount R := by
  simp only [recordedToffoliCount_append,recordedMeasurementCount_append,
    (embedRecorded_counts _).1,(embedRecorded_counts _).2,toffoliCount_reverse,measurementCount_reverse,
    ht,hm,Nat.add_zero,and_self]

theorem endpointSlot_counts (p ordinal : Nat) (slots : List HistoricalSlot) (E : RecordedProgram) :
    recordedToffoliCount (endpointSlotProgram p ordinal slots E)=
      recordedToffoliCount (seededAuthorWalkProgram p slots)+recordedToffoliCount E+
      recordedToffoliCount (seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots) ∧
    recordedMeasurementCount (endpointSlotProgram p ordinal slots E)=
      recordedMeasurementCount (seededAuthorWalkProgram p slots)+recordedMeasurementCount E+
      recordedMeasurementCount (seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots) :=
  splice_counts _ _ _ _ (closerProgram_counts _ _).1 (closerProgram_counts _ _).2

private theorem splice_run (W R E : RecordedProgram) (C : Program)
    (m : List Bool) (ordinal : Nat) (s : State) (hm : measurementCount C=0)
    (undo : run C.reverse (m.drop (ordinal+recordedMeasurementCount W+recordedMeasurementCount E))
      (runWithTape E m (ordinal+recordedMeasurementCount W)
        (run C (m.drop (ordinal+recordedMeasurementCount W)) (runWithTape W m ordinal s)))=
      runWithTape W m ordinal s)
    (back : runWithTape R m (ordinal+recordedMeasurementCount W+recordedMeasurementCount E)
      (runWithTape W m ordinal s)=s) :
    runWithTape (W++embedRecorded C++E++embedRecorded C.reverse++R) m ordinal s=s := by
  simp only [runWithTape_append,recordedMeasurementCount_append,runWithTape_embedRecorded,
    (embedRecorded_counts _).2,measurementCount_reverse,hm,Nat.add_zero,←Nat.add_assoc]
  rw [undo]
  exact back

/-- The entire splice restores the state before initialization. Coprimality is
an explicit caller premise and is not inferred merely from a good trajectory. -/
theorem endpointSlot_roundtrip {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (coprime : Int.gcd p (input x)=1) (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x) (E : RecordedProgram)
    (contract : EndpointContract p ordinal slots E m
      (runWithTape (seededAuthorWalkProgram p slots) m ordinal s)) :
    runWithTape (endpointSlotProgram p ordinal slots E) m ordinal s=s := by
  have endpoint := seededAuthorWalk_closer_endpoint input p hp x odd coprime good slots compiled s m ordinal ready encoding
  have widths := compileAuthorWalk_exit_widths slots compiled
  have positive : 0<p := by
    by_contra bad
    have zero : p=0 := by omega
    simp [zero] at odd
  have fw : 1<2^(walkExitBank walkSeedBank slots).f.payload.length := by rw [widths.1]; decide
  have pw : p<2^(walkExitBank walkSeedBank slots).gv.payload.length := by
    rw [widths.2.2.2]
    exact lt_trans hp (Nat.pow_lt_pow_right (by decide) (by decide))
  have undo := closerProgram_unclose (walkExitBank walkSeedBank slots) p
    (compileAuthorWalk_exit_owned slots compiled).1 fw positive pw _ _
    (m.drop (endpointCursor p ordinal slots+recordedMeasurementCount E))
    endpoint.1 endpoint.2.1 endpoint.2.2 contract.restored
  exact splice_run _ _ _ _ m ordinal s (closerProgram_counts _ _).2 undo
    (seededAuthorWalk_actual_reverse input p hp x odd good slots compiled s m ordinal _ ready encoding)

end ECDSAAdd.Arithmetic.Paper935
