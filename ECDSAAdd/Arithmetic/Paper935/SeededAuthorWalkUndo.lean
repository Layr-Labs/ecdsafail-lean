import ECDSAAdd.Arithmetic.Paper935.AuthorWalkArithmeticUndo
import ECDSAAdd.Arithmetic.Paper935.SeededAuthorWalkRun
import ECDSAAdd.Arithmetic.Paper935.WalkSeedInverse

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

def seededAuthorWalkReverse (p : Nat) (decoder : Nat → HistoricalSlot → Program)
    (ordinal : Nat) (slots : List HistoricalSlot) : RecordedProgram :=
  historicalWalkReverse walkRegisters decoder 0 ordinal slots ++ embedRecorded (unseedWalk p)

/-- Include real initialization and its cleanup in the complete State round
trip. Only the explicit history-decoder obligations remain conditional. -/
theorem seededAuthorWalk_reverse_of_history {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal cursor : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x)
    (decoder : Nat → HistoricalSlot → Program)
    (history : WalkHistoryUndo walkRegisters decoder m 0 ordinal cursor
      (run (seedWalk p) (m.drop ordinal) s) slots) :
    runWithTape (seededAuthorWalkReverse p decoder ordinal slots) m cursor
      (runWithTape (seededAuthorWalkProgram p slots) m ordinal s)=s := by
  have seed := seedWalk_run p hp s (m.drop ordinal) ready
  rw [encoding] at seed
  have undo := compileAuthorWalk_reverse_of_history input p x odd good slots compiled
    (run (seedWalk p) (m.drop ordinal) s) m ordinal cursor seed.2.1 seed.2.2.2 seed.2.2.1 decoder history
  rw [seededAuthorWalkProgram,runWithTape_append,runWithTape_embedRecorded,
    (embedRecorded_counts _).2,seedWalk_measurements,Nat.add_zero]
  rw [seededAuthorWalkReverse,runWithTape_append,undo,runWithTape_embedRecorded]
  exact seedWalk_roundtrip p hp s _ _

end ECDSAAdd.Arithmetic.Paper935
