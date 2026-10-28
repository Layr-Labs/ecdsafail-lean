import ECDSAAdd.Arithmetic.Paper935.OutputCapacity
import ECDSAAdd.Arithmetic.Paper935.OutputUncloser

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

/-- Reserve the output, then temporary workspace. Only the temporary set is
released; the output remains owned by the retained arena. -/
def EndpointOutputBorrow (A : Arena) (O : Finset Wire) (E : RecordedProgram) (out : State) : Prop :=
  ∃ retained : Arena, ∃ temporary : Finset Wire, ∃ during : Arena,
    A.reserve O=some retained ∧ temporary⊆arenaWires\retained.live ∧
    retained.reserve temporary=some during ∧ recordedWires E⊆during.live ∧
    during.release temporary out.basis=some retained

/-- This conditional contract supplies no output placement or endpoint gates.
The isolation obligation is stronger than freedom at the closed boundary. -/
structure EndpointOutputContract (p ordinal : Nat) (slots : List HistoricalSlot)
    (E : RecordedProgram) (O : Finset Wire) (v : BasisState) (m : List Bool) (s : State) : Prop where
  isolated : O⊆retainedOutputSpace p ordinal slots
  wellFormed : RecordedWellFormedAt (endpointCursor p ordinal slots) E
  arena : recordedWires E⊆arenaWires
  restored : OutputUncloserReady O (walkExitBank walkSeedBank slots)
    (runWithTape (seededAuthorWalkProgram p slots) m ordinal s) (endpointAfter p ordinal slots E m s)
  output : ∀ q∈O,(endpointAfter p ordinal slots E m s).basis q=v q
  borrow : EndpointOutputBorrow (authorClosedArena slots) O E (endpointAfter p ordinal slots E m s)

attribute [local irreducible] seededAuthorWalkProgram seededAuthorWalkReverse closerProgram actualHistoryDecoder

private theorem splice_output (W R E : RecordedProgram) (C : Program)
    (O : Finset Wire) (v : BasisState) (m : List Bool) (k : Nat) (s : State)
    (hm : measurementCount C=0)
    (isolated : Disjoint O (recordedWires (embedRecorded C.reverse++R)))
    (out : runWithTape E m (k+recordedMeasurementCount W)
      (run C (m.drop (k+recordedMeasurementCount W)) (runWithTape W m k s))=
      withOutput O v (run C (m.drop (k+recordedMeasurementCount W)) (runWithTape W m k s)))
    (undo : run C.reverse (m.drop (k+recordedMeasurementCount W+recordedMeasurementCount E))
      (run C (m.drop (k+recordedMeasurementCount W)) (runWithTape W m k s))=runWithTape W m k s)
    (back : runWithTape R m (k+recordedMeasurementCount W+recordedMeasurementCount E)
      (runWithTape W m k s)=s) :
    runWithTape (W++embedRecorded C++E++embedRecorded C.reverse++R) m k s=withOutput O v s := by
  have commute := runWithTape_withOutput (embedRecorded C.reverse++R) O v
    (run C (m.drop (k+recordedMeasurementCount W)) (runWithTape W m k s)) m
    (k+recordedMeasurementCount W+recordedMeasurementCount E) isolated
  simp only [runWithTape_append,runWithTape_embedRecorded,(embedRecorded_counts _).2,
    measurementCount_reverse,hm,Nat.add_zero] at commute
  simp only [runWithTape_append,recordedMeasurementCount_append,runWithTape_embedRecorded,
    (embedRecorded_counts _).2,measurementCount_reverse,hm,Nat.add_zero,←Nat.add_assoc]
  rw [out,commute,undo,back]

/-- Exact phase and all non-output bits are restored; the declared output is
retained. The theorem remains conditional on a concrete isolated placement. -/
theorem endpointSlot_withOutput {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (coprime : Int.gcd p (input x)=1) (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x) (E : RecordedProgram)
    (O : Finset Wire) (v : BasisState) (contract : EndpointOutputContract p ordinal slots E O v m s) :
    runWithTape (endpointSlotProgram p ordinal slots E) m ordinal s=withOutput O v s := by
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
  have outputEq := contract.restored.eq_withOutput O v (walkExitBank walkSeedBank slots) p
    (compileAuthorWalk_exit_owned slots compiled).1 fw positive pw _ _
    (m.drop (endpointCursor p ordinal slots)) endpoint.1 endpoint.2.1 endpoint.2.2 contract.output
  have isolated : Disjoint O (recordedWires
      (embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p).reverse ++
        seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots)) := by
    apply Finset.disjoint_left.mpr
    intro q hq hr
    exact (Finset.mem_sdiff.mp (contract.isolated hq)).2 (Finset.mem_union_right _ hr)
  exact splice_output _ _ _ _ O v m ordinal s (closerProgram_counts _ _).2 isolated outputEq
    (closerProgram_roundtrip _ _ (compileAuthorWalk_exit_owned slots compiled).1 _ _ _)
    (seededAuthorWalk_actual_reverse input p hp x odd good slots compiled s m ordinal _ ready encoding)

end ECDSAAdd.Arithmetic.Paper935
