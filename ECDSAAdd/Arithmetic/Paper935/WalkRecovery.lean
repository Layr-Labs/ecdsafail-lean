import ECDSAAdd.Arithmetic.Paper935.HistoricalWalkResources
import ECDSAAdd.Arithmetic.Paper935.AuthorWalkCompiler
import ECDSAAdd.Arithmetic.Paper935.ReadyHistory
import ECDSAAdd.Arithmetic.Paper935.PublicSlotInverse

namespace ECDSAAdd.Arithmetic.Paper935

/-- Recover the forgotten branch using its ORIGINAL absolute record, then pop
stored history. The decoder is an actual supplied gate program. -/
def HistoryLayout.recovery (H : HistoryLayout) (decoder : Program) (ordinal : Nat) : RecordedProgram :=
  ECDSAAdd.Arithmetic.Divsteps.recoverBranch decoder H.port
    (ordinal+measurementCount (storePush H.one H.zz H.pos H.sign H.output H.port
      H.zb H.frozen H.positive H.low H.record)) ++
    embedRecorded (storePop H.one H.zz H.pos H.sign H.output H.port H.zb H.frozen H.positive H.low H.record)

/-- A local interface discharged by the existing ready recovery theorem.
It states full State equality, including the phase, at the actual two cursors. -/
def HistoryUndoAt (H : HistoryLayout) (decoder : Program) (m : List Bool)
    (ordinal cursor : Nat) (s : State) : Prop :=
  runWithTape (H.recovery decoder ordinal) m cursor (runWithTape H.program m ordinal s)=s

/-- History is undone before the compiled arithmetic inverse. -/
def HistoricalSlot.undo (Q : HistoricalSlot) (F : SlotRegisters) (decoder : Program)
    (ordinal : Nat) : RecordedProgram :=
  Q.history.recovery decoder (ordinal+measurementCount (Q.slot.program F)) ++
    embedRecorded (Q.slot.inverse F)

/-- Only the two single-stage obligations are assumed, not a walk inverse. -/
structure SlotUndoConditions (Q : HistoricalSlot) (F : SlotRegisters) (decoder : Program)
    (m : List Bool) (ordinal cursor : Nat) (s : State) : Prop where
  arithmetic : ∀ n, run (Q.slot.inverse F) n (run (Q.slot.program F) (m.drop ordinal) s)=s
  history : HistoryUndoAt Q.history decoder m (ordinal+measurementCount (Q.slot.program F)) cursor
    (run (Q.slot.program F) (m.drop ordinal) s)

theorem HistoricalSlot.undo_run (Q : HistoricalSlot) (F : SlotRegisters) (decoder : Program)
    (m : List Bool) (ordinal cursor : Nat) (s : State)
    (h : SlotUndoConditions Q F decoder m ordinal cursor s) :
    runWithTape (Q.undo F decoder ordinal) m cursor (runWithTape (Q.program F) m ordinal s)=s := by
  rw [HistoricalSlot.program,runWithTape_append,runWithTape_embedRecorded,(embedRecorded_counts _).2]
  rw [HistoricalSlot.undo,runWithTape_append]
  rw [show runWithTape (Q.history.recovery decoder (ordinal+measurementCount (Q.slot.program F))) m cursor
      (runWithTape Q.history.program m (ordinal+measurementCount (Q.slot.program F))
        (run (Q.slot.program F) (m.drop ordinal) s))=run (Q.slot.program F) (m.drop ordinal) s from h.history]
  rw [runWithTape_embedRecorded]
  exact h.arithmetic _

/-- Forward offsets increase in forward order even though the emitted inverse
is concatenated in reverse order. Deferred source indices are never relocated. -/
def historicalWalkReverse (F : SlotRegisters) (decoder : Nat → HistoricalSlot → Program) :
    Nat → Nat → List HistoricalSlot → RecordedProgram
  | _,_,[] => []
  | index,ordinal,Q::rest =>
      historicalWalkReverse F decoder (index+1) (ordinal+recordedMeasurementCount (Q.program F)) rest ++
        Q.undo F (decoder index Q) ordinal

/-- Conditions are evaluated on the ACTUAL successive forward states and on
the reverse cursors determined by the emitted tail. They are not independent
state witnesses that might fail to connect at a boundary. -/
def WalkUndoConditions (F : SlotRegisters) (decoder : Nat → HistoricalSlot → Program)
    (m : List Bool) : Nat → Nat → Nat → State → List HistoricalSlot → Prop
  | _,_,_,_,[] => True
  | index,ordinal,cursor,s,Q::rest =>
      SlotUndoConditions Q F (decoder index Q) m ordinal
        (cursor+recordedMeasurementCount (historicalWalkReverse F decoder (index+1)
          (ordinal+recordedMeasurementCount (Q.program F)) rest)) s ∧
      WalkUndoConditions F decoder m (index+1) (ordinal+recordedMeasurementCount (Q.program F)) cursor
        (runWithTape (Q.program F) m ordinal s) rest

/-- Full basis and phase round trip by reverse-list induction. The same global
tape supplies saved old records and fresh inverse measurements at distinct cursors. -/
theorem historicalWalk_reverse_run (F : SlotRegisters) (decoder : Nat → HistoricalSlot → Program)
    (slots : List HistoricalSlot) (m : List Bool) (index ordinal cursor : Nat) (s : State)
    (h : WalkUndoConditions F decoder m index ordinal cursor s slots) :
    runWithTape (historicalWalkReverse F decoder index ordinal slots) m cursor
      (runWithTape (historicalWalkProgram F slots) m ordinal s)=s := by
  induction slots generalizing index ordinal cursor s with
  | nil => rfl
  | cons Q rest ih =>
    change runWithTape (_ ++ _) m cursor (runWithTape (Q.program F++historicalWalkProgram F rest) m ordinal s)=s
    rw [runWithTape_append,runWithTape_append,ih _ _ _ _ h.2]
    exact Q.undo_run F (decoder index Q) m ordinal _ s h.1

/-- Executing the concatenated forward and backward programs restores the
input State, with the reverse cursor set by the actual forward measurement count. -/
theorem historicalWalk_forward_reverse_run (F : SlotRegisters)
    (decoder : Nat → HistoricalSlot → Program) (slots : List HistoricalSlot)
    (m : List Bool) (index ordinal : Nat) (s : State)
    (h : WalkUndoConditions F decoder m index ordinal
      (ordinal+recordedMeasurementCount (historicalWalkProgram F slots)) s slots) :
    runWithTape (historicalWalkProgram F slots ++ historicalWalkReverse F decoder index ordinal slots)
      m ordinal s=s := by
  rw [runWithTape_append]
  exact historicalWalk_reverse_run F decoder slots m index ordinal _ s h

/-- Specialize to the actual returned 533-slot list. Success is used only for
the length and identity of that list, never as a substitute for inverse semantics. -/
theorem compileAuthorWalk_reverse_run (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (decoder : Nat → HistoricalSlot → Program) (m : List Bool) (ordinal : Nat) (s : State)
    (h : WalkUndoConditions walkRegisters decoder m 0 ordinal
      (ordinal+recordedMeasurementCount (historicalWalkProgram walkRegisters slots)) s slots) :
    slots.length=533 ∧
    runWithTape (historicalWalkReverse walkRegisters decoder 0 ordinal slots) m
      (ordinal+recordedMeasurementCount (historicalWalkProgram walkRegisters slots))
      (runWithTape (historicalWalkProgram walkRegisters slots) m ordinal s)=s := by
  exact ⟨(compileAuthorWalk_lengths slots compiled).1,
    historicalWalk_reverse_run walkRegisters decoder slots m 0 ordinal _ s h⟩

end ECDSAAdd.Arithmetic.Paper935
