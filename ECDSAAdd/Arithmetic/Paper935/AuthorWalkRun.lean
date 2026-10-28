import ECDSAAdd.Arithmetic.Paper935.AuthorWalkNumericalInputs

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget
attribute [local irreducible] historicalBudgets historicalNumericalInputs

/-- Successful original input labels determine the entire actual forward
execution: no per-slot encoding, state, stack-value or compiler-fit oracle is
assumed. The initial seeded encoding is the sole state representation premise. -/
theorem compileAuthorWalk_run {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (x : X) (odd : p%2=1)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : walkSeedArena.Ready s.basis)
    (rows : walkSeedBank.Encodes s.basis (zSeed p (input x)))
    (values : walkRegisters.Values s.basis ⟨zSeed p (input x),false,0⟩) :
    let t := runWithTape (historicalWalkProgram walkRegisters slots) m ordinal s
    walkRegisters.Values t.basis (pinWalk 498 p (input x) 533) ∧
    (walkExitArena walkSeedArena slots).Ready t.basis ∧
    (walkExitBank walkSeedBank slots).Encodes t.basis (pinWalk 498 p (input x) 533).rows ∧
    regValue (walkExitRecord [] slots) t.basis=trajectoryHistory 498 7 p (input x) 533 := by
  have budgets : historicalBudgets walkRegisters 6 walkSeedArena.live.card (bankWidths walkSeedBank) ([] : List Wire).length
      authorHistoricalRequests := by
    rw [walkSeed_card,walkSeed_widths,List.length_nil]
    exact authorHistoricalBudgets
  have numerical : historicalNumericalInputs walkRegisters 498 p (input x) 0 (bankWidths walkSeedBank) ([] : List Wire).length
      authorHistoricalRequests := by
    rw [walkSeed_widths,List.length_nil]
    exact authorNumericalInputs_good input p x good
  have result := compileHistoricalWalk_run walkRegisters 6 498 p (input x) walkSeedArena walkSeedBank [] authorHistoricalRequests
    slots compiled (by decide +kernel) odd walkSeed_distinct walkSeed_owned budgets 0 numerical s m ordinal ready rows values
    (by simp [regValue,trajectoryHistory])
  simpa only [authorHistoricalRequests_length,Nat.zero_add] using result

/-- The same forward-value statement together with actual compiler existence. -/
theorem authorWalk_good_run {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (x : X) (odd : p%2=1)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : walkSeedArena.Ready s.basis)
    (rows : walkSeedBank.Encodes s.basis (zSeed p (input x)))
    (values : walkRegisters.Values s.basis ⟨zSeed p (input x),false,0⟩) :
    ∃ slots,compileAuthorWalk=some slots ∧ slots.length=533 ∧
      let t := runWithTape (historicalWalkProgram walkRegisters slots) m ordinal s
      walkRegisters.Values t.basis (pinWalk 498 p (input x) 533) ∧
      (walkExitArena walkSeedArena slots).Ready t.basis ∧
      (walkExitBank walkSeedBank slots).Encodes t.basis (pinWalk 498 p (input x) 533).rows ∧
      regValue (walkExitRecord [] slots) t.basis=trajectoryHistory 498 7 p (input x) 533 := by
  obtain ⟨slots,compiled⟩ := compileAuthorWalk_exists
  exact ⟨slots,compiled,(compileAuthorWalk_lengths slots compiled).1,
    compileAuthorWalk_run input p x odd good slots compiled s m ordinal ready rows values⟩

end ECDSAAdd.Arithmetic.Paper935
