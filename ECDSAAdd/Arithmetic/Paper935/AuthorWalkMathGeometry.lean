import ECDSAAdd.Arithmetic.Paper935.WalkMathGeometry
import ECDSAAdd.Arithmetic.Paper935.AuthorWalkStaticTotal

namespace ECDSAAdd.Arithmetic.Paper935
attribute [local irreducible] historicalBudgets

/-- Every slot of the actual author walk satisfies the address-only conditions
used by the arithmetic semantics. Numerical fit and encoding remain separate. -/
theorem compileAuthorWalk_mathChecks (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots) :
    ∀ Q∈slots,Q.slot.StaticMathChecks walkRegisters := by
  apply compileHistoricalWalk_mathChecks walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests
    slots compiled (by decide +kernel) walkSeed_distinct walkSeed_owned
  rw [List.length_nil,walkSeed_card,walkSeed_widths]
  exact authorHistoricalBudgets

/-- Compiler success and static arithmetic geometry hold together without an
input-state or compiler-success hypothesis. -/
theorem authorWalk_staticMath :
    ∃ slots,compileAuthorWalk=some slots ∧ slots.length=533 ∧
      ∀ Q∈slots,Q.slot.StaticMathChecks walkRegisters := by
  obtain ⟨slots,compiled⟩ := compileAuthorWalk_exists
  exact ⟨slots,compiled,(compileAuthorWalk_lengths slots compiled).1,compileAuthorWalk_mathChecks slots compiled⟩

end ECDSAAdd.Arithmetic.Paper935
