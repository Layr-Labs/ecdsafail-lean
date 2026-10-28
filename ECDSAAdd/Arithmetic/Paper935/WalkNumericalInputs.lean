import ECDSAAdd.Arithmetic.Paper935.HistoricalSlotStaticRun
import ECDSAAdd.Arithmetic.Paper935.HistoricalWalkResources

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- Pure mathematical success conditions for one public request. No actual
intermediate state or execution result occurs in these fields. -/
structure HistoricalNumericalStep (F : SlotRegisters) (tmin : Nat) (p x : Int)
    (index : Nat) (before : RowWindow) (historyLength : Nat) (r : HistoricalRequest) : Prop where
  armed : r.armed=decide (tmin≤ index)
  offset : r.offset=index+1-tmin
  inputRows : before.Fits (pinWalk tmin p x index).rows
  exitRows : (historyWindow r.exitWidth).Fits (pinWalk tmin p x (index+1)).rows
  counter : PayloadFits (F.counter.length-1) (pinWalk tmin p x (index+1)).rows.z
  push : trajectoryStore tmin 7 p x index=true →
    2*trajectoryHistory tmin 7 p x index+(parityControl (pinWalk tmin p x index).rows).toNat<
      2^(max r.capacity historyLength)

def historicalNumericalInputs (F : SlotRegisters) (tmin : Nat) (p x : Int) :
    Nat → RowWindow → Nat → List HistoricalRequest → Prop
  | _,_,_,[] => True
  | index,before,n,r::rs => HistoricalNumericalStep F tmin p x index before n r ∧
      historicalNumericalInputs F tmin p x (index+1) (historyWindow r.exitWidth) (max r.capacity n) rs

/-- Final persistent views follow the same slot list as the actual compiler. -/
def walkExitArena : Arena → List HistoricalSlot → Arena
  | A,[] => A
  | _,Q::rest => walkExitArena Q.historyArena rest

def walkExitBank : WindowBank → List HistoricalSlot → WindowBank
  | b,[] => b
  | _,Q::rest => walkExitBank Q.slot.front.exitBank rest

def walkExitRecord : List Wire → List HistoricalSlot → List Wire
  | record,[] => record
  | _,Q::rest => walkExitRecord Q.history.record rest

end ECDSAAdd.Arithmetic.Paper935
