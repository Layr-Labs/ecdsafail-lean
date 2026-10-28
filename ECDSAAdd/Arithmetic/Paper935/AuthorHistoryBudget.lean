import ECDSAAdd.Arithmetic.Paper935.AuthorWalkStages
import ECDSAAdd.Arithmetic.Paper935.HistoryBudget

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

private theorem historyLength_shift (initial : Nat) (request : Nat → Nat) (t : Nat) :
    historyLength (max (request 0) initial) (fun i => request (i+1)) t =
      historyLength initial request (t+1) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [historyLength,ih]

/-- Compare the list-based allocation recurrence with the budget's indexed
recurrence only where the list actually has a stage. -/
theorem grownCapacities_historyCapacity (initial : Nat) (rs : List HistoricalRequest)
    (request : Nat → Nat) (agree : ∀ t,t<rs.length → (rs[t]?.getD ⟨initialWindow,0,false,0⟩).capacity=request t) :
    ∀ t,t<rs.length → (grownCapacities initial rs)[t]?=some (historyCapacity initial request t) := by
  induction rs generalizing initial request with
  | nil => intro t ht; simp at ht
  | cons r rs ih =>
    intro t ht
    have head : r.capacity=request 0 := by simpa using agree 0 (by simp)
    cases t with
    | zero => simp [grownCapacities,historyCapacity,historyLength,head]
    | succ t =>
      have tail := ih (max r.capacity initial) (fun i => request (i+1))
        (fun i hi => by simpa using agree (i+1) (by simpa using Nat.succ_lt_succ hi))
        t (by simpa using ht)
      simpa only [grownCapacities,List.getElem?_cons_succ,historyCapacity,head,historyLength_shift] using tail

def authorHistoryRequestAt (t : Nat) : Nat := historyRequest (authorSpans[t]?.getD 0) t

/-- The compiler's concrete 533-stage capacity equals the indexed budget
capacity on precisely those 533 indices; no claim is made past the list end. -/
theorem authorHistoryCapacityAt_eq (t : Nat) (ht : t<533) :
    authorHistoryCapacityAt t=historyCapacity 0 authorHistoryRequestAt t := by
  have eq := grownCapacities_historyCapacity 0 authorHistoricalRequests authorHistoryRequestAt
    (fun i hi => by
      have inside : i<533 := by simpa only [authorHistoricalRequests_length] using hi
      simp only [authorHistoricalRequests_at i inside,Option.getD_some,authorHistoryRequestAt])
    t (by simpa only [authorHistoricalRequests_length] using ht)
  simp only [authorHistoryCapacityAt,eq,Option.getD_some]

/-- Events inspect only existing stage indices, so the two capacities give
identical failures despite different definitions outside the compiled range. -/
theorem authorHistoryFailure_iff (p x : Int) :
    HistoryFailure 498 7 533 authorHistoryCapacityAt p x ↔
      HistoryFailure 498 7 533 (historyCapacity 0 authorHistoryRequestAt) p x := by
  constructor <;> rintro ⟨t,ht,hs,hbad⟩
  · exact ⟨t,ht,hs,by simpa only [authorHistoryCapacityAt_eq t ht] using hbad⟩
  · exact ⟨t,ht,hs,by simpa only [authorHistoryCapacityAt_eq t ht] using hbad⟩

/-- Original-label accounting for this concrete schedule. The seven-site
signed counter includes its sign; row-window events remain conservative. -/
noncomputable def authorTrajectoryEvents {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) : FailureEvents X :=
  trajectoryEvents input p 498 7 533 7 authorHistoryCapacityAt authorWindows

/-- The symbolic budget is exactly the existing union's mass. -/
theorem authorTrajectoryBudget_total {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (μ : InputLaw X) :
    (trajectoryBounds input p 498 7 533 7 authorHistoryCapacityAt authorWindows μ).total =
      μ.mass (authorTrajectoryEvents input p).bad := by
  exact trajectoryBounds_total input p 498 7 533 7 authorHistoryCapacityAt authorWindows μ

/-- A proven bound with per-stage requests transfers to the actual retained
record schedule. This uses a lower bound on capacity, not the resource cap 60. -/
theorem authorTrajectory_mass_le_requests {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (μ : InputLaw X) :
    μ.mass (authorTrajectoryEvents input p).bad ≤
      μ.mass (trajectoryEvents input p 498 7 533 7 authorHistoryRequestAt authorWindows).bad := by
  apply trajectory_mass_capacity_mono input p 498 7 533 7 authorHistoryRequestAt
    authorHistoryCapacityAt authorWindows μ
  intro t ht
  rw [authorHistoryCapacityAt_eq t ht]
  exact Nat.le_max_left _ _

/-- Every returned slot gets its numerical push premise from the SAME original
input's declared event. The state and stack-value hypotheses must still be
established by full arithmetic induction; compiler success alone is insufficient. -/
theorem compileAuthorWalk_history_fit {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (x : X)
    (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (t : Nat) (Q : HistoricalSlot) (atSlot : slots[t]?=some Q)
    (s : BasisState)
    (values : walkRegisters.OutputValues s (pinWalk 498 p (input x) t) (pinWalk 498 p (input x) (t+1)))
    (rows : Q.slot.front.exitBank.Encodes s (pinWalk 498 p (input x) (t+1)).rows)
    (inv : Inv p (pinWalk 498 p (input x) (t+1)).rows)
    (oldOdd : (pinWalk 498 p (input x) t).rows.f%2=1)
    (history : regValue Q.history.record s=trajectoryHistory 498 7 p (input x) t) :
    Q.history.selected s=true →
      2*regValue Q.history.record s+(s Q.history.port).toNat<2^Q.history.record.length := by
  obtain ⟨ht,C,bank,previous,hc⟩ := compileAuthorWalk_stage slots compiled t Q atSlot
  have h := (compileCheckedHistoricalSlot_contract C bank previous (bankWidths bank).addPad
    (historyWindow (authorWindows[t]?.getD initialWindow)) walkRegisters (decide (498≤t)) 6
    (t+1-498) (authorHistoryRequestAt t) Q hc).1
  have selector := compileHistoricalSlot_selector C bank previous (bankWidths bank).addPad
    (historyWindow (authorWindows[t]?.getD initialWindow)) walkRegisters (decide (498≤t)) 6
    (t+1-498) (authorHistoryRequestAt t) Q h
    (pinWalk 498 p (input x) t) (pinWalk 498 p (input x) (t+1)) s values rows p inv
  have contract := compileHistoricalSlot_contract C bank previous (bankWidths bank).addPad
    (historyWindow (authorWindows[t]?.getD initialWindow)) walkRegisters (decide (498≤t)) 6
    (t+1-498) (authorHistoryRequestAt t) Q h
  have grow := compileGrowingHistory_contract Q.slot.front.exitArena Q.historyArena Q.detectorArena previous
    Q.detectorWork (authorHistoryRequestAt t) walkRegisters.one walkRegisters.work0 walkRegisters.work1
    (walkRegisters.counter.getLastD 0) walkRegisters.active walkRegisters.parity walkRegisters.frozen
    walkRegisters.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history contract.2.2.2.2.2
  have ids := compileHistory_identity walkRegisters.one walkRegisters.work0 walkRegisters.work1
    (walkRegisters.counter.getLastD 0) walkRegisters.active walkRegisters.parity walkRegisters.frozen
    walkRegisters.counter (Q.slot.front.exitBank.fv.wires.drop 1 |>.take 6) Q.history.record Q.detectorWork
    Q.history grow.2.2
  have branch : s Q.history.port=parityControl (pinWalk 498 p (input x) t).rows := by
    rw [ids.2.2.2.2.2,values.parity]
    unfold bbit parityControl
    split_ifs with swap
    · rw [oldOdd,swap.2]
    · rfl
  have noFail : ¬HistoryFailure 498 7 533 authorHistoryCapacityAt p (input x) := by
    intro bad
    exact good ((mem_trajectory_bad input p 498 7 533 7 authorHistoryCapacityAt authorWindows x).mpr
      (Or.inr (Or.inl bad)))
  rw [selector,history,branch,compileAuthorWalk_capacity_at slots compiled t Q atSlot]
  exact (no_history_failure_iff 498 7 533 authorHistoryCapacityAt p (input x)).mp noFail t ht

end ECDSAAdd.Arithmetic.Paper935
