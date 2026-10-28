import ECDSAAdd.Arithmetic.Paper935.AuthorWalkRun
import ECDSAAdd.Arithmetic.Paper935.WalkDecoderUndo
import ECDSAAdd.Arithmetic.Paper935.AuthorWalkArithmeticUndo

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget
attribute [local irreducible] historicalBudgets historicalNumericalInputs decoderBudgets

/-- All actual history decoders recover on the existing good-input event. -/
theorem compileAuthorWalk_history_undo {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (x : X) (odd : p%2=1)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal cursor : Nat) (ready : walkSeedArena.Ready s.basis)
    (rows : walkSeedBank.Encodes s.basis (zSeed p (input x)))
    (values : walkRegisters.Values s.basis ⟨zSeed p (input x),false,0⟩) :
    WalkHistoryUndo walkRegisters (actualHistoryDecoder walkRegisters p) m 0 ordinal cursor s slots := by
  have budgets : historicalBudgets walkRegisters 6 walkSeedArena.live.card (bankWidths walkSeedBank) ([] : List Wire).length
      authorHistoricalRequests := by
    rw [walkSeed_card,walkSeed_widths,List.length_nil]
    exact authorHistoricalBudgets
  have numerical : historicalNumericalInputs walkRegisters 498 p (input x) 0 (bankWidths walkSeedBank) ([] : List Wire).length
      authorHistoricalRequests := by
    rw [walkSeed_widths,List.length_nil]
    exact authorNumericalInputs_good input p x good
  have decoderBudget : decoderBudgets walkSeedArena.live.card (bankWidths walkSeedBank) ([] : List Wire).length
      authorHistoricalRequests := by
    rw [walkSeed_card,walkSeed_widths,List.length_nil]
    exact authorDecoderBudgets
  have noEarly := (trajectory_good input p 498 7 533 7 authorHistoryCapacityAt authorWindows x good).2.2.1
  have result := compileHistoricalWalk_history_undo walkRegisters 6 p (input x) walkSeedArena walkSeedBank [] authorHistoricalRequests
    slots compiled (by decide +kernel) (by decide +kernel) odd walkSeed_distinct walkSeed_owned budgets decoderBudget
    noEarly 0 (by rw [authorHistoricalRequests_length]) numerical s m ordinal cursor ready rows values
    (by simp [regValue,trajectoryHistory])
  simpa only [authorHistoricalRequests_length,Nat.zero_add] using result

/-- The actual author walk and constructed decoder reverse restore basis and
phase on good inputs. No arithmetic or history inverse oracle remains. -/
theorem compileAuthorWalk_actual_reverse {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (x : X) (odd : p%2=1)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal cursor : Nat) (ready : walkSeedArena.Ready s.basis)
    (rows : walkSeedBank.Encodes s.basis (zSeed p (input x)))
    (values : walkRegisters.Values s.basis ⟨zSeed p (input x),false,0⟩)
 :
    runWithTape (historicalWalkReverse walkRegisters (actualHistoryDecoder walkRegisters p) 0 ordinal slots) m cursor
      (runWithTape (historicalWalkProgram walkRegisters slots) m ordinal s)=s := by
  exact historicalWalk_reverse_of_parts walkRegisters (actualHistoryDecoder walkRegisters p) m 0 ordinal cursor s slots
    (compileAuthorWalk_arithmetic_undo input p x odd good slots compiled s m ordinal ready rows values)
    (compileAuthorWalk_history_undo input p x odd good slots compiled s m ordinal cursor ready rows values)

end ECDSAAdd.Arithmetic.Paper935
