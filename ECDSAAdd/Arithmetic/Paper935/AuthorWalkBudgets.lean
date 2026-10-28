import ECDSAAdd.Arithmetic.Paper935.WalkStaticBudget
import ECDSAAdd.Arithmetic.Paper935.AuthorWalkCompiler

namespace ECDSAAdd.Arithmetic.Paper935

/-- Kernel-checked public capacity inequalities for all 533 actual requests. -/
theorem authorHistoricalBudgets :
    historicalBudgets walkRegisters 6 794 initialWindow 0 authorHistoricalRequests := by
  decide +kernel

theorem walkSeed_distinct :
    (walkRegisters.wires++[]++walkSeedBank.rows.flatMap WindowRow.wires).Nodup := by decide +kernel

theorem walkSeed_owned :
    (walkRegisters.wires++[]++walkSeedBank.rows.flatMap WindowRow.wires).toFinset⊆walkSeedArena.live := by decide +kernel

theorem walkSeed_card : walkSeedArena.live.card=794 := by decide +kernel

theorem walkSeed_widths : bankWidths walkSeedBank=initialWindow := by decide +kernel

end ECDSAAdd.Arithmetic.Paper935
