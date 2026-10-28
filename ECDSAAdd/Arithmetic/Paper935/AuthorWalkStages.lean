import ECDSAAdd.Arithmetic.Paper935.AuthorHistoryCapacity

namespace ECDSAAdd.Arithmetic.Paper935

theorem HistoricalWalkCompiled.stage (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (h : HistoricalWalkCompiled F probeWidth A b record requests slots)
    (t : Nat) (Q : HistoricalSlot) (r : HistoricalRequest)
    (hs : slots[t]?=some Q) (hr : requests[t]?=some r) :
    ∃ C bank previous, compileCheckedHistoricalSlot C bank previous (bankWidths bank).addPad
      (historyWindow r.exitWidth) F r.armed probeWidth r.offset r.capacity=some Q := by
  induction h generalizing t with
  | nil => simp at hs
  | cons A b record request requests slot slots head tail ih =>
    cases t with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hs hr
      subst Q
      subst r
      exact ⟨A,b,record,head⟩
    | succ t =>
      exact ih t (by simpa only [List.getElem?_cons_succ] using hs)
        (by simpa only [List.getElem?_cons_succ] using hr)

theorem authorHistoricalRequests_at (t : Nat) (ht : t<533) :
    authorHistoricalRequests[t]?=some
      { exitWidth:=authorWindows[t]?.getD initialWindow,
        capacity:=historyRequest (authorSpans[t]?.getD 0) t,
        armed:=decide (498≤t), offset:=t+1-498 } := by
  simp [authorHistoricalRequests,ht]

/-- Each compiled slot is the actual checked compiler call at precisely its
public index, including freeze threshold, offset and history request. -/
theorem compileAuthorWalk_stage (slots : List HistoricalSlot) (h : compileAuthorWalk=some slots)
    (t : Nat) (Q : HistoricalSlot) (hs : slots[t]?=some Q) :
    t<533 ∧ ∃ C bank previous,
      compileCheckedHistoricalSlot C bank previous (bankWidths bank).addPad
        (historyWindow (authorWindows[t]?.getD initialWindow)) walkRegisters (decide (498≤t)) 6
        (t+1-498) (historyRequest (authorSpans[t]?.getD 0) t)=some Q := by
  have len := (compileAuthorWalk_lengths slots h).1
  have inside : t<slots.length := (List.getElem?_eq_some_iff.mp hs).1
  have ht : t<533 := by omega
  let r : HistoricalRequest :=
    { exitWidth:=authorWindows[t]?.getD initialWindow,
      capacity:=historyRequest (authorSpans[t]?.getD 0) t,
      armed:=decide (498≤t), offset:=t+1-498 }
  have req : authorHistoricalRequests[t]?=some r := authorHistoricalRequests_at t ht
  have contract := compileHistoricalWalk_contract walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests slots h
  have stage := HistoricalWalkCompiled.stage walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests slots contract t Q r hs req
  exact ⟨ht,stage⟩

end ECDSAAdd.Arithmetic.Paper935
