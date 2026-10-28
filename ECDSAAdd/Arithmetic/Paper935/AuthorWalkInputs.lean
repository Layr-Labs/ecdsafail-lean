import ECDSAAdd.Arithmetic.Paper935.AuthorWalkRun
import ECDSAAdd.Arithmetic.Paper935.WalkForwardInputs

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget
attribute [local irreducible] historicalBudgets historicalNumericalInputs

/-- Connected initial-state invariants for every actual author slot. -/
theorem compileAuthorWalk_inputs {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (x : X) (odd : p%2=1)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : walkSeedArena.Ready s.basis)
    (rows : walkSeedBank.Encodes s.basis (zSeed p (input x)))
    (values : walkRegisters.Values s.basis ⟨zSeed p (input x),false,0⟩) :
    WalkForwardInputs walkRegisters 498 p (input x) m 0 ordinal s walkSeedArena walkSeedBank [] slots := by
  have budgets : historicalBudgets walkRegisters 6 walkSeedArena.live.card (bankWidths walkSeedBank) ([] : List Wire).length
      authorHistoricalRequests := by
    rw [walkSeed_card,walkSeed_widths,List.length_nil]
    exact authorHistoricalBudgets
  have numerical : historicalNumericalInputs walkRegisters 498 p (input x) 0 (bankWidths walkSeedBank) ([] : List Wire).length
      authorHistoricalRequests := by
    rw [walkSeed_widths,List.length_nil]
    exact authorNumericalInputs_good input p x good
  have result := compileHistoricalWalk_inputs walkRegisters 6 498 p (input x) walkSeedArena walkSeedBank [] authorHistoricalRequests
    slots compiled (by decide +kernel) odd walkSeed_distinct walkSeed_owned budgets 0 numerical s m ordinal ready rows values
    (by simp [regValue,trajectoryHistory])
  simpa only [authorHistoricalRequests_length,Nat.zero_add] using result

end ECDSAAdd.Arithmetic.Paper935
