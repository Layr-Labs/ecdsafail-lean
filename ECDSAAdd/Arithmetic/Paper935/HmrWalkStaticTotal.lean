import ECDSAAdd.Arithmetic.Paper935.WalkWidthStaticBudget
import ECDSAAdd.Arithmetic.Paper935.HmrWalkCompiler

namespace ECDSAAdd.Arithmetic.Paper935

/-- Kernel certificate for the allocation budgets of the six-bit-counter,
five-threshold instance over all 533 public steps. -/
theorem hmrHistoricalBudgets :
    historicalBudgetsWidth 4 hmrWalkRegisters 6 793 initialWindow 0 authorHistoricalRequests := by
  decide +kernel

theorem hmrWalkSeed_distinct :
    (hmrWalkRegisters.wires++[]++walkSeedBank.rows.flatMap WindowRow.wires).Nodup := by decide +kernel

theorem hmrWalkSeed_owned :
    (hmrWalkRegisters.wires++[]++walkSeedBank.rows.flatMap WindowRow.wires).toFinset⊆hmrWalkSeedArena.live := by decide +kernel

theorem hmrWalkSeed_card : hmrWalkSeedArena.live.card=793 := by decide +kernel

theorem hmrWalkSeed_widths : bankWidths walkSeedBank=initialWindow := by decide +kernel

private theorem budget_transport (hw : Nat) (F : SlotRegisters) (probeWidth live live' n n' : Nat)
    (before before' : RowWindow) (requests : List HistoricalRequest)
    (hl : live=live') (hb : before=before') (hn : n=n')
    (h : historicalBudgetsWidth hw F probeWidth live' before' n' requests) :
    historicalBudgetsWidth hw F probeWidth live before n requests := by
  subst live'
  subst before'
  subst n'
  exact h

attribute [local irreducible] historicalBudgetsWidth

/-- Actual successful compilation is derived, rather than supplied as a
premise. This is a compiler-existence certificate, not full source equivalence. -/
theorem compileHmrWalk_exists : ∃ slots,compileHmrWalk=some slots := by
  apply compileHistoricalWalkWidth_static_exists 4 hmrWalkRegisters 6 hmrWalkSeedArena walkSeedBank [] authorHistoricalRequests
  · decide +kernel
  · exact hmrWalkSeed_distinct
  · exact hmrWalkSeed_owned
  · exact budget_transport 4 hmrWalkRegisters 6 hmrWalkSeedArena.live.card 793 ([] : List Wire).length 0
      (bankWidths walkSeedBank) initialWindow authorHistoricalRequests
      hmrWalkSeed_card hmrWalkSeed_widths rfl hmrHistoricalBudgets

end ECDSAAdd.Arithmetic.Paper935
