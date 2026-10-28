import ECDSAAdd.Arithmetic.Paper935.BorrowGeometry

namespace ECDSAAdd.Arithmetic.Paper935

/-- Counts for an arbitrary list of declared live sets. These sets need not
fit a particular physical arena; correspondence to execution is separate. -/
def liveCensus (trace : List (Finset Wire)) : List Nat := trace.map Finset.card

def censusPeak : List Nat → Nat
  | [] => 0
  | n::ns => max n (censusPeak ns)

def livePeak (trace : List (Finset Wire)) : Nat := censusPeak (liveCensus trace)

theorem censusPeak_append (xs ys : List Nat) :
    censusPeak (xs++ys)=max (censusPeak xs) (censusPeak ys) := by
  induction xs with
  | nil => simp [censusPeak]
  | cons x xs ih => simp [censusPeak,ih,max_assoc]

theorem censusPeak_le_iff (xs : List Nat) (bound : Nat) :
    censusPeak xs≤bound ↔ ∀n∈xs,n≤bound := by
  induction xs with
  | nil => simp [censusPeak]
  | cons x xs ih => simp [censusPeak,ih]

theorem livePeak_append (xs ys : List (Finset Wire)) :
    livePeak (xs++ys)=max (livePeak xs) (livePeak ys) := by
  simp [livePeak,liveCensus,censusPeak_append]

/-- Sequential stage peaks combine by max, not by summing storage that may
be reused at different times. Every stage must include its interior census. -/
theorem livePeak_stages (stages : List (List (Finset Wire))) :
    livePeak stages.flatten=censusPeak (stages.map livePeak) := by
  induction stages with
  | nil => rfl
  | cons stage stages ih => simp [List.flatten_cons,livePeak_append,ih,censusPeak]

theorem livePeak_le_iff (trace : List (Finset Wire)) (bound : Nat) :
    livePeak trace≤bound ↔ ∀live∈trace,live.card≤bound := by
  simp [livePeak,liveCensus,censusPeak_le_iff]

/-- Simultaneously live components add only when their physical sets are
separate. This must not be confused with sequential stage composition. -/
theorem census_disjoint (a b : Finset Wire) (separate : Disjoint a b) :
    livePeak [a∪b]=a.card+b.card := by
  simp [livePeak,liveCensus,censusPeak,Finset.card_union_of_disjoint separate]

theorem Arena.reserve_card (A B : Arena) (qs : Finset Wire)
    (h : A.reserve qs=some B) : B.live.card=A.live.card+qs.card := by
  unfold Arena.reserve at h
  split at h
  next valid =>
    cases h
    exact Finset.card_union_of_disjoint valid.2
  next => simp at h

theorem Arena.release_card (A B : Arena) (qs : Finset Wire) (s : BasisState)
    (h : A.release qs s=some B) : B.live.card+qs.card=A.live.card := by
  unfold Arena.release at h
  split at h
  next valid =>
    cases h
    simp only
    rw [Finset.card_sdiff_of_subset valid.1]
    exact Nat.sub_add_cancel (Finset.card_le_card valid.1)
  next => simp at h

/-- Arithmetic budget check only. Passing this does not certify that a
particular allocator call succeeds or that the borrowed wires are clean. -/
def Arena.withinBudget (A : Arena) (n budget : Nat) : Bool :=
  decide (A.live.card+n≤budget)

theorem Arena.withinBudget_iff (A : Arena) (n budget : Nat) :
    A.withinBudget n budget=true ↔ A.live.card+n≤budget := by
  simp [Arena.withinBudget]

theorem Arena.borrowMany_census (A B : Arena) (n : Nat) (qs : List Wire)
    (borrow : A.borrowMany n=some (B,qs)) :
    livePeak [A.live,B.live]=A.live.card+n := by
  rw [show livePeak [A.live,B.live]=max A.live.card B.live.card by
    simp [livePeak,liveCensus,censusPeak]]
  rw [(A.borrowMany_live B n qs borrow).2]
  omega

theorem Arena.borrowMany_withinBudget_iff (A B : Arena) (n budget : Nat) (qs : List Wire)
    (borrow : A.borrowMany n=some (B,qs)) :
    livePeak [A.live,B.live]≤budget ↔ A.withinBudget n budget=true := by
  rw [A.borrowMany_census B n qs borrow,A.withinBudget_iff]

/-- A reservation, followed by actual cleaning and a successful release,
has its maximum at the reserved state. This is independent of the cap. -/
theorem Arena.reserve_release_peak (A B C : Arena) (borrowed released : Finset Wire)
    (s : BasisState) (reserve : A.reserve borrowed=some B)
    (release : B.release released s=some C) :
    livePeak [A.live,B.live,C.live]=A.live.card+borrowed.card := by
  have hb := A.reserve_card B borrowed reserve
  have hc := B.release_card C released s release
  simp only [livePeak,liveCensus,List.map_cons,List.map_nil,censusPeak,Nat.max_zero]
  omega

/-- Exact census composition for any list of Arena-stage traces. No assertion
that these declared traces exhaust the execution is smuggled into the bound. -/
theorem arenaChain_peak (stages : List (List Arena)) :
    livePeak ((stages.map (List.map Arena.live)).flatten)=
      censusPeak (stages.map (fun stage => livePeak (stage.map Arena.live))) := by
  rw [livePeak_stages,List.map_map]
  rfl

end ECDSAAdd.Arithmetic.Paper935
