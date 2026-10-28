import ECDSAAdd.Arithmetic.Paper935.HistoryCompilerLengths

namespace ECDSAAdd.Arithmetic.Paper935

/-- Physical exits retain enough signed coefficient sites to read the actual
six-bit history predicate. Resizing emits real sign extension when needed. -/
def historyWindow (w : RowWindow) : RowWindow := {w with fv:=max 7 w.fv}

def bankWidths (b : WindowBank) : RowWindow :=
  ⟨b.f.payload.length,b.g.payload.length,b.fv.payload.length,b.gv.payload.length⟩

structure HistoricalRequest where
  exitWidth : RowWindow
  capacity : Nat
  armed : Bool
  offset : Nat

/-- This compiler threads the actual exit bank, post-growth arena and grown
record into the next call. Detector pools are not retained across slots. -/
def compileHistoricalWalk (F : SlotRegisters) (probeWidth : Nat) :
    Arena → WindowBank → List Wire → List HistoricalRequest → Option (List HistoricalSlot)
  | _,_,_,[] => some []
  | A,b,record,r::rs => do
      let Q ← compileCheckedHistoricalSlot A b record (bankWidths b).addPad
        (historyWindow r.exitWidth) F r.armed probeWidth r.offset r.capacity
      let rest ← compileHistoricalWalk F probeWidth Q.historyArena Q.slot.front.exitBank Q.history.record rs
      pure (Q::rest)

inductive HistoricalWalkCompiled (F : SlotRegisters) (probeWidth : Nat) :
    Arena → WindowBank → List Wire → List HistoricalRequest → List HistoricalSlot → Prop
  | nil (A b record) : HistoricalWalkCompiled F probeWidth A b record [] []
  | cons (A b record r rs Q rest)
      (head : compileCheckedHistoricalSlot A b record (bankWidths b).addPad
        (historyWindow r.exitWidth) F r.armed probeWidth r.offset r.capacity=some Q)
      (tail : HistoricalWalkCompiled F probeWidth Q.historyArena Q.slot.front.exitBank Q.history.record rs rest) :
      HistoricalWalkCompiled F probeWidth A b record (r::rs) (Q::rest)

theorem compileHistoricalWalk_contract (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (h : compileHistoricalWalk F probeWidth A b record requests=some slots) :
    HistoricalWalkCompiled F probeWidth A b record requests slots := by
  induction requests generalizing A b record slots with
  | nil => simp only [compileHistoricalWalk,Option.some.injEq] at h; subst slots; exact .nil A b record
  | cons r rs ih =>
    unfold compileHistoricalWalk at h
    obtain ⟨Q,hq,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest,hr,h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    exact .cons A b record r rs Q rest hq (ih _ _ _ _ hr)

/-- The capacity schedule is the running maximum of actual allocation
requests and the initial record length, rather than the requests themselves. -/
def grownCapacities : Nat → List HistoricalRequest → List Nat
  | _,[] => []
  | n,r::rs => let k := max r.capacity n; k::grownCapacities k rs

theorem HistoricalWalkCompiled.lengths (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (h : HistoricalWalkCompiled F probeWidth A b record requests slots) :
    slots.length=requests.length ∧
    slots.map (fun Q => Q.history.record.length)=grownCapacities record.length requests := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | cons A b record r rs Q rest head tail ih =>
    have hc := (compileCheckedHistoricalSlot_contract A b record (bankWidths b).addPad
      (historyWindow r.exitWidth) F r.armed probeWidth r.offset r.capacity Q head).1
    have len := (compileHistoricalSlot_lengths A b record (bankWidths b).addPad
      (historyWindow r.exitWidth) F r.armed probeWidth r.offset r.capacity Q hc).1
    constructor
    · simp only [List.length_cons,ih.1]
    · simp only [List.map_cons,grownCapacities,ih.2,len]

end ECDSAAdd.Arithmetic.Paper935
