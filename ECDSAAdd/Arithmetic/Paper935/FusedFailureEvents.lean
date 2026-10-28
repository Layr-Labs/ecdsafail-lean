import ECDSAAdd.Arithmetic.Paper935.FusedEndpointModel

namespace ECDSAAdd.Arithmetic.Paper935
open FailureBudget

/-- engine.py:2948, :3296, :2999 and :3174, respectively. These four causes
extend an existing ledger; they do not redefine any of its first five cells. -/
structure FusedFailures (X : Type*) where
  row : Finset X
  lift : Finset X
  horner : Finset X
  sign : Finset X

variable {X : Type*} [DecidableEq X]

/-- engine.py:3254: aggregate enabled mathematical calls on the SAME original
label. An inverse replay shares its forward mathematical call, not fresh data. -/
noncomputable def fusedFailures [Fintype X] (calls : X → List FusedCall) : FusedFailures X := by
  classical
  exact ⟨Finset.univ.filter (fun x => ∃ c∈calls x,c.enabled=true ∧ ¬c.RowGood),
    Finset.univ.filter (fun x => ∃ c∈calls x,c.enabled=true ∧ ¬c.LiftGood),
    Finset.univ.filter (fun x => ∃ c∈calls x,c.enabled=true ∧ ¬c.HornerGood),
    Finset.univ.filter (fun x => ∃ c∈calls x,c.enabled=true ∧ ¬c.SignGood)⟩

/-- Ordered union of the four new source-derived causes. -/
def FusedFailures.bad (f : FusedFailures X) : Finset X := f.row∪f.lift∪f.horner∪f.sign

/-- Cells six through nine remove the unchanged old union, then prior causes. -/
def FusedFailures.exclusiveAfter (f : FusedFailures X) (old : Finset X) : FusedFailures X :=
  ⟨f.row\old, f.lift\(old∪f.row), f.horner\(old∪f.row∪f.lift),
    f.sign\(old∪f.row∪f.lift∪f.horner)⟩

theorem FusedFailures.partition (f : FusedFailures X) (old : Finset X) :
    old∪f.bad=old∪(f.exclusiveAfter old).bad := by
  ext x
  simp [FusedFailures.bad,FusedFailures.exclusiveAfter]
  tauto

theorem FusedFailures.exclusive_disjoint (f : FusedFailures X) (old : Finset X) :
    Disjoint old (f.exclusiveAfter old).bad := by
  simp [Finset.disjoint_left,FusedFailures.bad,FusedFailures.exclusiveAfter]
  tauto

theorem FusedFailures.exclusive_pairwise (f : FusedFailures X) (old : Finset X) :
    [(f.exclusiveAfter old).row,(f.exclusiveAfter old).lift,
      (f.exclusiveAfter old).horner,(f.exclusiveAfter old).sign].Pairwise Disjoint := by
  simp [List.pairwise_cons,Finset.disjoint_left,FusedFailures.exclusiveAfter]
  tauto

/-- The original five cells and the four appended cells remain pairwise
 disjoint without editing the old event definitions. -/
theorem fused_nine_pairwise (e : FailureEvents X) (scaling : Finset X)
    (f : FusedFailures X) :
    [e.exclusive.counter,e.exclusive.history,e.exclusive.deadline,e.exclusive.window,
      scalingExclusive e scaling,
      (f.exclusiveAfter (scalingBad e scaling)).row,
      (f.exclusiveAfter (scalingBad e scaling)).lift,
      (f.exclusiveAfter (scalingBad e scaling)).horner,
      (f.exclusiveAfter (scalingBad e scaling)).sign].Pairwise Disjoint := by
  simp [List.pairwise_cons,Finset.disjoint_left,FailureEvents.exclusive,
    scalingExclusive,scalingBad,FailureEvents.mem_bad,FusedFailures.exclusiveAfter]
  tauto

/-- No mass estimates or independence assumptions: only exact disjoint sums. -/
theorem FusedFailures.mass_partition [Fintype X] (f : FusedFailures X)
    (old : Finset X) (μ : InputLaw X) :
    μ.mass (old∪f.bad)=μ.mass old+
      (((μ.mass (f.exclusiveAfter old).row+μ.mass (f.exclusiveAfter old).lift)+
        μ.mass (f.exclusiveAfter old).horner)+μ.mass (f.exclusiveAfter old).sign) := by
  rw [f.partition old]
  change (∑ x∈old∪(f.exclusiveAfter old).bad,μ.weight x)=_
  rw [Finset.sum_union (f.exclusive_disjoint old)]
  congr 1
  unfold FusedFailures.bad
  rw [Finset.sum_union,Finset.sum_union,Finset.sum_union]
  all_goals simp [Finset.disjoint_left,FusedFailures.exclusiveAfter]
  all_goals tauto

/-- New source events are appended after the existing five-class accounting. -/
theorem fused_nine_mass [Fintype X] (e : FailureEvents X) (scaling : Finset X)
    (f : FusedFailures X) (μ : InputLaw X) :
    μ.mass (scalingBad e scaling∪f.bad)=
      (((μ.mass e.exclusive.counter+μ.mass e.exclusive.history)+μ.mass e.exclusive.deadline)+
        μ.mass e.exclusive.window+μ.mass (scalingExclusive e scaling))+
      (((μ.mass (f.exclusiveAfter (scalingBad e scaling)).row+
        μ.mass (f.exclusiveAfter (scalingBad e scaling)).lift)+
        μ.mass (f.exclusiveAfter (scalingBad e scaling)).horner)+
        μ.mass (f.exclusiveAfter (scalingBad e scaling)).sign) := by
  rw [f.mass_partition,scalingBad_mass]

/-- Outside the new union, every enabled modeled invocation satisfies all
four numerical checks. This is not a physical-circuit correctness theorem. -/
theorem fusedFailures_good [Fintype X] (calls : X → List FusedCall) (x : X) :
    x∉(fusedFailures calls).bad ↔
      ∀ c∈calls x,c.enabled=true → c.RowGood ∧ c.LiftGood ∧ c.HornerGood ∧ c.SignGood := by
  classical
  simp [fusedFailures,FusedFailures.bad]
  aesop

end ECDSAAdd.Arithmetic.Paper935
