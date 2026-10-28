import ECDSAAdd.Arithmetic.Paper935.AuthorWalkCompiler

namespace ECDSAAdd.Arithmetic.Paper935

/-- Capacity derived by the same running-max recurrence as actual allocation. -/
def authorHistoryCapacityAt (t : Nat) : Nat :=
  (grownCapacities 0 authorHistoricalRequests)[t]?.getD 0

theorem HistoricalWalkCompiled.capacity_at (F : SlotRegisters) (probeWidth : Nat)
    (A : Arena) (b : WindowBank) (record : List Wire) (requests : List HistoricalRequest)
    (slots : List HistoricalSlot) (h : HistoricalWalkCompiled F probeWidth A b record requests slots)
    (t : Nat) (Q : HistoricalSlot) (ht : slots[t]?=some Q) :
    (grownCapacities record.length requests)[t]?=some Q.history.record.length := by
  have eq := congrArg (fun xs : List Nat => xs[t]?) (h.lengths F probeWidth A b record requests slots).2
  simpa only [List.getElem?_map,ht,Option.map_some] using eq.symm

theorem compileAuthorWalk_capacity_at (slots : List HistoricalSlot) (h : compileAuthorWalk=some slots)
    (t : Nat) (Q : HistoricalSlot) (ht : slots[t]?=some Q) :
    Q.history.record.length=authorHistoryCapacityAt t := by
  have contract := compileHistoricalWalk_contract walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests slots h
  have cap := contract.capacity_at walkRegisters 6 walkSeedArena walkSeedBank [] authorHistoricalRequests slots t Q ht
  simp only [List.length_nil] at cap
  simp only [authorHistoryCapacityAt,cap,Option.getD_some]

theorem grownCapacities_bound (initial limit : Nat) (requests : List HistoricalRequest)
    (hi : initial≤limit) (hr : ∀ r∈requests,r.capacity≤limit) :
    ∀ k∈grownCapacities initial requests,k≤limit := by
  induction requests generalizing initial with
  | nil => simp [grownCapacities]
  | cons r rs ih =>
    have hmax : max r.capacity initial≤limit := max_le (hr r (by simp)) hi
    intro k hk
    simp only [grownCapacities,List.mem_cons] at hk
    rcases hk with rfl|hk
    · exact hmax
    · exact ih _ hmax (fun r h => hr r (List.mem_cons_of_mem _ h)) k hk

theorem authorHistoryCapacityAt_bound (t : Nat) : authorHistoryCapacityAt t≤60 := by
  have all : ∀ r∈authorHistoricalRequests,r.capacity≤60 := by
    intro r hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    exact historyRequest_bound _ _
  have bound := grownCapacities_bound 0 60 authorHistoricalRequests (by omega) all
  unfold authorHistoryCapacityAt
  cases h : (grownCapacities 0 authorHistoricalRequests)[t]? with
  | none => simp
  | some k => exact bound k (List.mem_of_getElem? h)

end ECDSAAdd.Arithmetic.Paper935
