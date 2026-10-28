import ECDSAAdd.Arithmetic.Paper935.WalkNumericalBounds
import ECDSAAdd.Arithmetic.Paper935.AuthorHistoryBudget

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget
attribute [local irreducible] historicalNumericalInputs

/-- The existing declared failure event supplies every numerical condition of
the actual 533-step execution recurrence on the same original input label. -/
theorem authorNumericalInputs_good {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (x : X) (good : x∉(authorTrajectoryEvents input p).bad) :
    historicalNumericalInputs walkRegisters 498 p (input x) 0 initialWindow 0 authorHistoricalRequests := by
  obtain ⟨counter,push,_,_,seed,windows⟩ := trajectory_good input p 498 7 533 7 authorHistoryCapacityAt authorWindows x good
  apply historicalNumericalInputs_of_bounds walkRegisters 498 p (input x) 0 initialWindow 0 authorHistoricalRequests seed
  intro t r hr
  simp only [Nat.zero_add]
  have inside : t<533 := by
    have h := (List.getElem?_eq_some_iff.mp hr).1
    simpa only [authorHistoricalRequests_length] using h
  have expected := authorHistoricalRequests_at t inside
  have eq : r=⟨authorWindows[t]?.getD initialWindow,
      historyRequest (authorSpans[t]?.getD 0) t,
      decide (498≤t),t+1-498⟩ := Option.some.inj (hr.symm.trans expected)
  subst r
  refine ⟨rfl,rfl,?_,?_,?_⟩
  · have ht : t<authorWindows.length := by rw [author_lengths.1]; exact inside
    have hw : authorWindows[t]?=some authorWindows[t] := List.getElem?_eq_some_iff.mpr ⟨ht,rfl⟩
    have fit := windows t authorWindows[t] hw
    simp only [hw,Option.getD_some]
    apply fit.mono
    simp [RowWindow.Le,historyWindow]
  · simpa only [walkRegisters,List.length_range'] using counter (t+1) (by omega)
  · simpa only [authorHistoryCapacityAt] using push t inside

end ECDSAAdd.Arithmetic.Paper935
