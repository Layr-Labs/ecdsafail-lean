import ECDSAAdd.Math.Divsteps.Semantics

namespace ECDSAAdd.Divsteps

/-- Independent branch images, before key collisions are merged. -/
def prepareEntry (kv : Int × DSet) : Int × DSet × DSet :=
  (kv.1, DSet.ofList (kv.2.map evenTrans),
    if 0 < kv.1 then DSet.ofList (kv.2.map oddPosTrans)
    else DSet.ofList (kv.2.map oddNonposTrans))

def gatherEntries (entries : List (Int × DSet × DSet)) : State :=
  entries.foldl (fun acc (k, even, odd) =>
    let acc := joinState (2 + k) even acc
    if 0 < k then joinState (2 - k) odd acc else joinState (2 + k) odd acc) []

def finishEntry (M : Int) (kv : Int × DSet) : Option (Int × DSet) :=
  if narrow M kv.2 then none else some (kv.1, chainHull kv.2)

/-- Factoring the checker into separately certifiable row computations
changes no mathematical operation. This theorem does not assert that any
particular supplied row or full termination certificate passes. -/
theorem processDivstep_stages (M : Int) (s : State) :
    processDivstep M s =
      (gatherEntries (s.map prepareEntry)).filterMap (finishEntry M) := by
  simp only [processDivstep, gatherEntries, List.foldl_map]
  congr 1
  apply congrArg (fun f => List.foldl f ([] : State) s)
  funext acc kv
  rcases kv with ⟨k, v⟩
  by_cases hk : 0 < k <;> simp [prepareEntry, hk]

end ECDSAAdd.Divsteps
