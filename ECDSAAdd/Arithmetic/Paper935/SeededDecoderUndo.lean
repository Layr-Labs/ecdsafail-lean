import ECDSAAdd.Arithmetic.Paper935.AuthorDecoderUndo
import ECDSAAdd.Arithmetic.Paper935.SeededAuthorWalkUndo

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

/-- Real initialization, the actual walk and its constructed reverse restore
the full State on good inputs, with no history-decoder correctness premise. -/
theorem seededAuthorWalk_actual_reverse {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal cursor : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x)
 :
    runWithTape (seededAuthorWalkReverse p (actualHistoryDecoder walkRegisters p) ordinal slots) m cursor
      (runWithTape (seededAuthorWalkProgram p slots) m ordinal s)=s := by
  have seed := seedWalk_run p hp s (m.drop ordinal) ready
  rw [encoding] at seed
  have undo := compileAuthorWalk_actual_reverse input p x odd good slots compiled
    (run (seedWalk p) (m.drop ordinal) s) m ordinal cursor seed.2.1 seed.2.2.2 seed.2.2.1
  rw [seededAuthorWalkProgram,runWithTape_append,runWithTape_embedRecorded,
    (embedRecorded_counts _).2,seedWalk_measurements,Nat.add_zero]
  rw [seededAuthorWalkReverse,runWithTape_append,undo,runWithTape_embedRecorded]
  exact seedWalk_roundtrip p hp s _ _

end ECDSAAdd.Arithmetic.Paper935
