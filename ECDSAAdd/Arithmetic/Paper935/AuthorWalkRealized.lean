import ECDSAAdd.Arithmetic.Paper935.AuthorWalkStaticTotal
import ECDSAAdd.Arithmetic.Paper935.HistoricalWalkResources

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.RecordedQuantum

/-- Unconditional physical realization of the actual 533-slot emitted walk.
This is a circuit-formation result, not its arithmetic correctness. -/
theorem authorWalk_realized (ordinal : Nat) :
    ∃ slots, compileAuthorWalk=some slots ∧ slots.length=533 ∧
      ∃ l, ∃ c : Circuit 935 ordinal l,c.program=historicalWalkProgram walkRegisters slots := by
  obtain ⟨slots,compiled⟩ := compileAuthorWalk_exists
  exact ⟨slots,compiled,(compileAuthorWalk_lengths slots compiled).1,
    compileHistoricalWalk_realize walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests slots compiled ordinal⟩

end ECDSAAdd.Arithmetic.Paper935
