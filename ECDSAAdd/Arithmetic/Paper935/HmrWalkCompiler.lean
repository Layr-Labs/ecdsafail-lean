import ECDSAAdd.Arithmetic.Paper935.HistoricalWalkWidth
import ECDSAAdd.Arithmetic.Paper935.AuthorWalkCompiler

namespace ECDSAAdd.Arithmetic.Paper935

/-- circuit.py/HmrWalk parameter instance: six signed counter bits and
six stop-offset bits. This does not assert literal Hmr gate-list equality. -/
def hmrWalkRegisters : SlotRegisters :=
  { one:=774, frozen:=775, parity:=776, active:=777, swap:=778,
    work0:=779, work1:=780, counter:=List.range' 781 6, offset:=List.range' 787 6 }

def hmrWalkSeedArena : Arena := ⟨Finset.range 793,by
  intro q hq
  simp only [Finset.mem_range,arenaWires] at *
  omega⟩

/-- Hmr history stores at valuation at least five: read bits one through
four after arithmetic. Public windows/spans retain the pinned Hmr schedule. -/
def compileHmrWalk : Option (List HistoricalSlot) :=
  compileHistoricalWalkWidth 4 hmrWalkRegisters 6 hmrWalkSeedArena walkSeedBank [] authorHistoricalRequests

theorem hmrWalk_dials : hmrWalkRegisters.counter.length=6 ∧
    hmrWalkRegisters.offset.length=6 ∧ hmrWalkSeedArena.live.card=793 ∧
    authorHistoricalRequests.length=533 := by
  exact ⟨by decide,by decide,by decide +kernel,authorHistoricalRequests_length⟩

end ECDSAAdd.Arithmetic.Paper935
