import ECDSAAdd.Arithmetic.Paper935.HistoricalWalkCompiler
import ECDSAAdd.Arithmetic.Paper935.Seed

namespace ECDSAAdd.Arithmetic.Paper935

/-- Concrete seed bank uses the existing shared-host row seeding circuit. -/
def walkSeedBank : WindowBank :=
  ⟨⟨seedF,768⟩,⟨seedG,769⟩,⟨[772],770⟩,⟨[773],771⟩⟩

/-- Seven retained controls, a seven-site signed counter, and six offset bits.
These sites are outside the existing 774-site seeded row/host allocation. -/
def walkRegisters : SlotRegisters :=
  { one:=774, frozen:=775, parity:=776, active:=777, swap:=778,
    work0:=779, work1:=780, counter:=List.range' 781 7, offset:=List.range' 788 6 }

def walkSeedArena : Arena := ⟨Finset.range 794,by
  intro q hq
  simp only [Finset.mem_range,arenaWires] at *
  omega⟩

def authorHistoricalRequests : List HistoricalRequest :=
  (List.range 533).map fun t =>
    { exitWidth:=authorWindows[t]?.getD initialWindow,
      capacity:=historyRequest (authorSpans[t]?.getD 0) t,
      armed:=decide (498≤t), offset:=t+1-498 }

def compileAuthorWalk : Option (List HistoricalSlot) :=
  compileHistoricalWalk walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests

theorem authorHistoricalRequests_length : authorHistoricalRequests.length=533 := by
  simp [authorHistoricalRequests]

theorem compileAuthorWalk_lengths (slots : List HistoricalSlot) (h : compileAuthorWalk=some slots) :
    slots.length=533 ∧
    slots.map (fun Q => Q.history.record.length)=grownCapacities 0 authorHistoricalRequests := by
  have contract := compileHistoricalWalk_contract walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests slots h
  simpa only [authorHistoricalRequests_length,List.length_nil] using contract.lengths _ _ _ _ _ _ _


end ECDSAAdd.Arithmetic.Paper935
