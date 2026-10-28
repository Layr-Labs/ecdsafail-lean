import ECDSAAdd.Arithmetic.Paper935.CheckedHistoricalSlotWidth
import ECDSAAdd.Arithmetic.Paper935.HistoricalWalkCompiler

namespace ECDSAAdd.Arithmetic.Paper935

/-- Retain exactly the payload width required by the chosen history slice. -/
def historyWindowWidth (historyWidth : Nat) (w : RowWindow) : RowWindow :=
  {w with fv:=max (historyWidth+1) w.fv}

/-- This compiler threads the actual exit bank, post-growth arena and grown
record into the next call. Detector pools are not retained across slots. -/
def compileHistoricalWalkWidth (historyWidth : Nat) (F : SlotRegisters) (probeWidth : Nat) :
    Arena → WindowBank → List Wire → List HistoricalRequest → Option (List HistoricalSlot)
  | _,_,_,[] => some []
  | A,b,record,r::rs => do
      let Q ← compileCheckedHistoricalSlotWidth historyWidth A b record (bankWidths b).addPad
        (historyWindowWidth historyWidth r.exitWidth) F r.armed probeWidth r.offset r.capacity
      let rest ← compileHistoricalWalkWidth historyWidth F probeWidth Q.historyArena Q.slot.front.exitBank Q.history.record rs
      pure (Q::rest)

inductive HistoricalWalkCompiledWidth (historyWidth : Nat) (F : SlotRegisters) (probeWidth : Nat) :
    Arena → WindowBank → List Wire → List HistoricalRequest → List HistoricalSlot → Prop
  | nil (A b record) : HistoricalWalkCompiledWidth historyWidth F probeWidth A b record [] []
  | cons (A b record r rs Q rest)
      (head : compileCheckedHistoricalSlotWidth historyWidth A b record (bankWidths b).addPad
        (historyWindowWidth historyWidth r.exitWidth) F r.armed probeWidth r.offset r.capacity=some Q)
      (tail : HistoricalWalkCompiledWidth historyWidth F probeWidth Q.historyArena Q.slot.front.exitBank Q.history.record rs rest) :
      HistoricalWalkCompiledWidth historyWidth F probeWidth A b record (r::rs) (Q::rest)

theorem compileHistoricalWalkWidth_contract (historyWidth : Nat) (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (h : compileHistoricalWalkWidth historyWidth F probeWidth A b record requests=some slots) :
    HistoricalWalkCompiledWidth historyWidth F probeWidth A b record requests slots := by
  induction requests generalizing A b record slots with
  | nil => simp only [compileHistoricalWalkWidth,Option.some.injEq] at h; subst slots; exact .nil A b record
  | cons r rs ih =>
    unfold compileHistoricalWalkWidth at h
    obtain ⟨Q,hq,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest,hr,h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .cons A b record r rs Q rest hq (ih _ _ _ _ hr)

end ECDSAAdd.Arithmetic.Paper935
