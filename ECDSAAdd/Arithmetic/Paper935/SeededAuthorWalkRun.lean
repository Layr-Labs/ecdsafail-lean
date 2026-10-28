import ECDSAAdd.Arithmetic.Paper935.AuthorWalkRun
import ECDSAAdd.Arithmetic.Paper935.WalkSeed

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

/-- The actual seed gates followed by the compiled measured forward walk. -/
def seededAuthorWalkProgram (p : Nat) (slots : List HistoricalSlot) : RecordedProgram :=
  embedRecorded (seedWalk p) ++ historicalWalkProgram walkRegisters slots

/-- Original physical input encoding and the declared good event suffice for
initialization and all 533 forward slots, on every measurement tape. -/
theorem seededAuthorWalk_run {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x) :
    let t := runWithTape (seededAuthorWalkProgram p slots) m ordinal s
    walkRegisters.Values t.basis (pinWalk 498 p (input x) 533) ∧
    (walkExitArena walkSeedArena slots).Ready t.basis ∧
    (walkExitBank walkSeedBank slots).Encodes t.basis (pinWalk 498 p (input x) 533).rows ∧
    regValue (walkExitRecord [] slots) t.basis=trajectoryHistory 498 7 p (input x) 533 := by
  have seed := seedWalk_run p hp s (m.drop ordinal) ready
  rw [encoding] at seed
  have result := compileAuthorWalk_run input p x odd good slots compiled
    (run (seedWalk p) (m.drop ordinal) s) m
    (ordinal+recordedMeasurementCount (embedRecorded (seedWalk p))) seed.2.1 seed.2.2.2 seed.2.2.1
  simpa only [seededAuthorWalkProgram,runWithTape_append,runWithTape_embedRecorded] using result

end ECDSAAdd.Arithmetic.Paper935
