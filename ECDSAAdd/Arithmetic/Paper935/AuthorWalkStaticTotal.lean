import ECDSAAdd.Arithmetic.Paper935.AuthorWalkBudgets

namespace ECDSAAdd.Arithmetic.Paper935

private theorem budget_transport (F : SlotRegisters) (probeWidth live live' n n' : Nat)
    (before before' : RowWindow) (requests : List HistoricalRequest)
    (hl : live=live') (hw : before=before') (hn : n=n')
    (h : historicalBudgets F probeWidth live' before' n' requests) :
    historicalBudgets F probeWidth live before n requests := by
  subst live'
  subst before'
  subst n'
  exact h

attribute [local irreducible] historicalBudgets

/-- The actual compiler succeeds; no compiler result is assumed. -/
theorem compileAuthorWalk_exists : ∃ slots,compileAuthorWalk=some slots := by
  apply compileHistoricalWalk_static_exists walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests
  · decide +kernel
  · exact walkSeed_distinct
  · exact walkSeed_owned
  · exact budget_transport walkRegisters 6 walkSeedArena.live.card 794 ([] : List Wire).length 0
      (bankWidths walkSeedBank) initialWindow authorHistoricalRequests
      walkSeed_card walkSeed_widths rfl authorHistoricalBudgets

end ECDSAAdd.Arithmetic.Paper935
