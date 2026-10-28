import ECDSAAdd.Arithmetic.Paper935.AuthorWalkRun
import ECDSAAdd.Arithmetic.Paper935.WalkUndoAssembly

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget
attribute [local irreducible] historicalBudgets historicalNumericalInputs

/-- All arithmetic undo obligations on the actual original-label forward trajectory. -/
theorem compileAuthorWalk_arithmetic_undo {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (x : X) (odd : p%2=1)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : walkSeedArena.Ready s.basis)
    (rows : walkSeedBank.Encodes s.basis (zSeed p (input x)))
    (values : walkRegisters.Values s.basis ⟨zSeed p (input x),false,0⟩) :
    WalkArithmeticUndo walkRegisters m ordinal s slots := by
  have budgets : historicalBudgets walkRegisters 6 walkSeedArena.live.card (bankWidths walkSeedBank) ([] : List Wire).length
      authorHistoricalRequests := by
    rw [walkSeed_card,walkSeed_widths,List.length_nil]
    exact authorHistoricalBudgets
  have numerical : historicalNumericalInputs walkRegisters 498 p (input x) 0 (bankWidths walkSeedBank) ([] : List Wire).length
      authorHistoricalRequests := by
    rw [walkSeed_widths,List.length_nil]
    exact authorNumericalInputs_good input p x good
  have result := compileHistoricalWalk_arithmetic_undo walkRegisters 6 498 p (input x) walkSeedArena walkSeedBank [] authorHistoricalRequests
    slots compiled (by decide +kernel) odd walkSeed_distinct walkSeed_owned budgets 0 numerical s m ordinal ready rows values
    (by simp [regValue,trajectoryHistory])
  simpa only [authorHistoricalRequests_length,Nat.zero_add] using result

/-- The actual author walk restores the full State once its history decoder
obligations are discharged. No arithmetic inverse premises remain. -/
theorem compileAuthorWalk_reverse_of_history {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (x : X) (odd : p%2=1)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal cursor : Nat) (ready : walkSeedArena.Ready s.basis)
    (rows : walkSeedBank.Encodes s.basis (zSeed p (input x)))
    (values : walkRegisters.Values s.basis ⟨zSeed p (input x),false,0⟩)
    (decoder : Nat → HistoricalSlot → Program)
    (history : WalkHistoryUndo walkRegisters decoder m 0 ordinal cursor s slots) :
    runWithTape (historicalWalkReverse walkRegisters decoder 0 ordinal slots) m cursor
      (runWithTape (historicalWalkProgram walkRegisters slots) m ordinal s)=s := by
  exact historicalWalk_reverse_of_parts walkRegisters decoder m 0 ordinal cursor s slots
    (compileAuthorWalk_arithmetic_undo input p x odd good slots compiled s m ordinal ready rows values) history

end ECDSAAdd.Arithmetic.Paper935
