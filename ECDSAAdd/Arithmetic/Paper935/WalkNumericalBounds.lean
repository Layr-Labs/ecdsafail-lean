import ECDSAAdd.Arithmetic.Paper935.HistoricalWalkRun

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- Indexed bounds on the public requests imply the recursive numerical
predicate consumed by actual execution, including the exact running capacity. -/
theorem historicalNumericalInputs_of_bounds (F : SlotRegisters) (tmin : Nat) (p x : Int)
    (index : Nat) (before : RowWindow) (n : Nat) (requests : List HistoricalRequest)
    (seedFit : before.Fits (pinWalk tmin p x index).rows)
    (bounds : ∀ t r,requests[t]?=some r →
      r.armed=decide (tmin≤ index+t) ∧ r.offset=index+t+1-tmin ∧
      (historyWindow r.exitWidth).Fits (pinWalk tmin p x (index+t+1)).rows ∧
      PayloadFits (F.counter.length-1) (pinWalk tmin p x (index+t+1)).rows.z ∧
      (trajectoryStore tmin 7 p x (index+t)=true →
        2*trajectoryHistory tmin 7 p x (index+t)+(parityControl (pinWalk tmin p x (index+t)).rows).toNat<
          2^((grownCapacities n requests)[t]?.getD 0))) :
    historicalNumericalInputs F tmin p x index before n requests := by
  induction requests generalizing index before n with
  | nil => trivial
  | cons r rs ih =>
    have head := bounds 0 r (by simp)
    simp only [Nat.add_zero,grownCapacities,List.getElem?_cons_zero,Option.getD_some] at head
    refine ⟨⟨head.1,head.2.1,seedFit,head.2.2.1,head.2.2.2.1,head.2.2.2.2⟩,?_⟩
    apply ih (index+1) (historyWindow r.exitWidth) (max r.capacity n) head.2.2.1
    intro t rr hrr
    have h := bounds (t+1) rr (by simpa only [List.getElem?_cons_succ] using hrr)
    simpa only [grownCapacities,List.getElem?_cons_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

end ECDSAAdd.Arithmetic.Paper935
