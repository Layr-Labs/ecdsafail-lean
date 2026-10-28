import ECDSAAdd.Arithmetic.Paper935.WalkRecovery

namespace ECDSAAdd.Arithmetic.Paper935

/-- The deferred phase correction references the last measurement of the
forward history segment, strictly before that segment's final cursor. -/
theorem HistoryLayout.recovery_wellFormed (H : HistoryLayout) (decoder : Program)
    (ordinal cursor : Nat) (h : ordinal+recordedMeasurementCount H.program≤cursor) :
    RecordedWellFormedAt cursor (H.recovery decoder ordinal) := by
  have count : recordedMeasurementCount H.program=
      measurementCount (storePush H.one H.zz H.pos H.sign H.output H.port
        H.zb H.frozen H.positive H.low H.record)+1 := by
    simp only [HistoryLayout.program,storePushForget,recordedMeasurementCount_append,(embedRecorded_counts _).2]
    rfl
  rw [HistoryLayout.recovery,RecordedWellFormedAt_append]
  exact ⟨ECDSAAdd.Arithmetic.Divsteps.recoverBranch_wellFormed _ _ _ _ (by omega),embedRecorded_wellFormed _ _⟩

theorem HistoricalSlot.undo_wellFormed (Q : HistoricalSlot) (F : SlotRegisters) (decoder : Program)
    (ordinal cursor : Nat) (h : ordinal+recordedMeasurementCount (Q.program F)≤cursor) :
    RecordedWellFormedAt cursor (Q.undo F decoder ordinal) := by
  rw [HistoricalSlot.undo,RecordedWellFormedAt_append]
  refine ⟨Q.history.recovery_wellFormed decoder _ cursor ?_,embedRecorded_wellFormed _ _⟩
  simpa only [HistoricalSlot.program,recordedMeasurementCount_append,(embedRecorded_counts _).2,Nat.add_assoc] using h

/-- Every saved record read by the reversed list belongs to the already
completed forward walk. Inverse measurements advance their own cursor. -/
theorem historicalWalkReverse_wellFormed (F : SlotRegisters) (decoder : Nat → HistoricalSlot → Program)
    (slots : List HistoricalSlot) (index ordinal cursor : Nat)
    (h : ordinal+recordedMeasurementCount (historicalWalkProgram F slots)≤cursor) :
    RecordedWellFormedAt cursor (historicalWalkReverse F decoder index ordinal slots) := by
  induction slots generalizing index ordinal cursor with
  | nil => trivial
  | cons Q rest ih =>
    have count : recordedMeasurementCount (historicalWalkProgram F (Q::rest))=
        recordedMeasurementCount (Q.program F)+recordedMeasurementCount (historicalWalkProgram F rest) := by
      exact recordedMeasurementCount_append _ _
    rw [historicalWalkReverse,RecordedWellFormedAt_append]
    refine ⟨ih _ _ _ (by omega),Q.undo_wellFormed F (decoder index Q) _ _ (by omega)⟩

/-- The actual compiled forward walk followed by recovery has valid record
references at every position; this does not assert inverse support or cost. -/
theorem HistoricalWalkCompiled.forward_reverse_wellFormed
    (F : SlotRegisters) (probeWidth : Nat) (A : Arena) (b : WindowBank) (record : List Wire)
    (requests : List HistoricalRequest) (slots : List HistoricalSlot)
    (compiled : HistoricalWalkCompiled F probeWidth A b record requests slots)
    (decoder : Nat → HistoricalSlot → Program) (index ordinal : Nat) :
    RecordedWellFormedAt ordinal (historicalWalkProgram F slots ++
      historicalWalkReverse F decoder index ordinal slots) := by
  rw [RecordedWellFormedAt_append]
  exact ⟨(compiled.resources F probeWidth A b record requests slots ordinal).2.2,
    historicalWalkReverse_wellFormed F decoder slots index ordinal _ (Nat.le_refl _)⟩

end ECDSAAdd.Arithmetic.Paper935
