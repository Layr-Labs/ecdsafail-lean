import ECDSAAdd.Arithmetic.Paper935.WalkArithmeticUndo

namespace ECDSAAdd.Arithmetic.Paper935

/-- History-only obligations at the exact forward states and reverse cursors.
Arithmetic inversion is proved independently from the forward invariant. -/
def WalkHistoryUndo (F : SlotRegisters) (decoder : Nat → HistoricalSlot → Program)
    (m : List Bool) : Nat → Nat → Nat → State → List HistoricalSlot → Prop
  | _,_,_,_,[] => True
  | index,ordinal,cursor,s,Q::rest =>
      HistoryUndoAt Q.history (decoder index Q) m (ordinal+measurementCount (Q.slot.program F))
        (cursor+recordedMeasurementCount (historicalWalkReverse F decoder (index+1)
          (ordinal+recordedMeasurementCount (Q.program F)) rest))
        (run (Q.slot.program F) (m.drop ordinal) s) ∧
      WalkHistoryUndo F decoder m (index+1) (ordinal+recordedMeasurementCount (Q.program F)) cursor
        (runWithTape (Q.program F) m ordinal s) rest

theorem walkUndoConditions_of_parts (F : SlotRegisters) (decoder : Nat → HistoricalSlot → Program)
    (m : List Bool) (index ordinal cursor : Nat) (s : State) (slots : List HistoricalSlot)
    (arithmetic : WalkArithmeticUndo F m ordinal s slots)
    (history : WalkHistoryUndo F decoder m index ordinal cursor s slots) :
    WalkUndoConditions F decoder m index ordinal cursor s slots := by
  induction slots generalizing index ordinal cursor s with
  | nil => trivial
  | cons Q rest ih =>
    exact ⟨⟨arithmetic.1,history.1⟩,ih _ _ _ _ arithmetic.2 history.2⟩

theorem historicalWalk_reverse_of_parts (F : SlotRegisters) (decoder : Nat → HistoricalSlot → Program)
    (m : List Bool) (index ordinal cursor : Nat) (s : State) (slots : List HistoricalSlot)
    (arithmetic : WalkArithmeticUndo F m ordinal s slots)
    (history : WalkHistoryUndo F decoder m index ordinal cursor s slots) :
    runWithTape (historicalWalkReverse F decoder index ordinal slots) m cursor
      (runWithTape (historicalWalkProgram F slots) m ordinal s)=s := by
  exact historicalWalk_reverse_run F decoder slots m index ordinal cursor s
    (walkUndoConditions_of_parts F decoder m index ordinal cursor s slots arithmetic history)

end ECDSAAdd.Arithmetic.Paper935
