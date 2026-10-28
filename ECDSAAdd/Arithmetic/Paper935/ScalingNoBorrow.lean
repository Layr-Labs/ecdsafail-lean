import ECDSAAdd.Arithmetic.Paper935.FoldHalfMath
import ECDSAAdd.Arithmetic.Paper935.AuthorRiderSchedule
import ECDSAAdd.Arithmetic.Paper935.TrajectoryMass

namespace ECDSAAdd.Arithmetic.Paper935
open FailureBudget

/-- One mathematical low-window condition, shared by seam and rider. -/
def FoldNoBorrow (width c r : Nat) : Prop := r%2=1 → c-1≤r%2^width

/-- All active calls are checked at their mathematical input, including the
updates caused by earlier active calls. Inactive calls leave the value alone. -/
def ScalingNoBorrow (p width c : Nat) : List Bool → Nat → Prop
  | [],_ => True
  | active::rest,r =>
      (active=true → FoldNoBorrow width c r) ∧
      ScalingNoBorrow p width c rest (if active then halveMod p r else r)

instance scalingNoBorrowDecidable (p width c : Nat) (flags : List Bool) (r : Nat) :
    Decidable (ScalingNoBorrow p width c flags r) := by
  induction flags generalizing r with
  | nil => unfold ScalingNoBorrow; infer_instance
  | cons active rest ih => unfold ScalingNoBorrow FoldNoBorrow; infer_instance

theorem scalingNoBorrow_append (p width c : Nat) (a b : List Bool) (r : Nat) :
    ScalingNoBorrow p width c (a++b) r ↔
      ScalingNoBorrow p width c a r ∧
      ScalingNoBorrow p width c b (ECDSAAdd.Arithmetic.Divsteps.halveActive p a r) := by
  induction a generalizing r with
  | nil => simp [ScalingNoBorrow,ECDSAAdd.Arithmetic.Divsteps.halveActive]
  | cons active rest ih =>
    cases active <;> simp [ScalingNoBorrow,ECDSAAdd.Arithmetic.Divsteps.halveActive,ih,and_assoc]

/-- The exact 498-call seam followed by the reverse armed-window activity. -/
def authorScalingActivities (p : Nat) (x : Int) : List Bool :=
  List.replicate 498 true ++ authorRiderActivities p x

/-- A pure mathematical predicate; its seed is the value before the seam. -/
def AuthorScalingNoBorrow (p width c : Nat) (x : Int) (seed : Nat) : Prop :=
  ScalingNoBorrow p width c (authorScalingActivities p x) seed

theorem authorScalingNoBorrow_parts (p width c : Nat) (x : Int) (seed : Nat) :
    AuthorScalingNoBorrow p width c x seed ↔
      ScalingNoBorrow p width c (List.replicate 498 true) seed ∧
      ScalingNoBorrow p width c (authorRiderActivities p x) ((halveMod p)^[498] seed) := by
  rw [AuthorScalingNoBorrow,authorScalingActivities,scalingNoBorrow_append]
  rw [ECDSAAdd.Arithmetic.Divsteps.halveActive_eq]
  rw [List.count_replicate_self]

/-- Mathematical execution of the actual fold operation, for comparison with
ideal modular halving. This definition is not a circuit correctness claim. -/
def foldedActive (n width c : Nat) : List Bool → Nat → Nat
  | [],r => r
  | active::rest,r => foldedActive n width c rest (if active then foldedHalf n width c r else r)

theorem foldedActive_correct (n width c : Nat) (positive : 0<n) (cpos : 0<c)
    (csmall : c<2^n) (odd : c%2=1) (literal : c-1<2^width)
    (flags : List Bool) (r : Nat) (good : ScalingNoBorrow (2^n-c) width c flags r) :
    foldedActive n width c flags r=ECDSAAdd.Arithmetic.Divsteps.halveActive (2^n-c) flags r := by
  induction flags generalizing r with
  | nil => rfl
  | cons active rest ih =>
    cases active with
    | false => exact ih r good.2
    | true =>
      change foldedActive n width c rest (foldedHalf n width c r)=_
      rw [foldedHalf_correct n width c r positive cpos csmall odd literal (good.1 rfl)]
      exact ih _ good.2

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The seed is a mathematical function of the same original labels as input.
The physical register value is deliberately absent from this event. -/
noncomputable def authorScalingFailure (input : X → Int) (seed : X → Nat)
    (p width c : Nat) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => ¬AuthorScalingNoBorrow p width c (input x) (seed x))

omit [DecidableEq X] in
theorem mem_authorScalingFailure (input : X → Int) (seed : X → Nat)
    (p width c : Nat) (x : X) :
    x∈authorScalingFailure input seed p width c ↔ ¬AuthorScalingNoBorrow p width c (input x) (seed x) := by
  classical
  simp [authorScalingFailure]

omit [DecidableEq X] in
theorem not_mem_authorScalingFailure (input : X → Int) (seed : X → Nat)
    (p width c : Nat) (x : X) :
    x∉authorScalingFailure input seed p width c ↔ AuthorScalingNoBorrow p width c (input x) (seed x) := by
  rw [mem_authorScalingFailure]
  exact not_not

/-- Existing four causes and the new scaling cause, on one original label space. -/
def scalingBad (e : FailureEvents X) (scaling : Finset X) : Finset X := e.bad∪scaling

/-- Fifth exclusive cell, after the four existing ordered cells. -/
def scalingExclusive (e : FailureEvents X) (scaling : Finset X) : Finset X := scaling\e.bad

omit [Fintype X] in
theorem scalingExclusive_disjoint (e : FailureEvents X) (scaling : Finset X) :
    Disjoint e.bad (scalingExclusive e scaling) := by
  exact Finset.disjoint_left.mpr (fun _ h k => (Finset.mem_sdiff.mp k).2 h)

omit [Fintype X] in
theorem scalingBad_partition (e : FailureEvents X) (scaling : Finset X) :
    scalingBad e scaling=e.exclusive.bad∪scalingExclusive e scaling := by
  rw [FailureEvents.exclusive_bad]
  ext x
  simp [scalingBad,scalingExclusive]

omit [Fintype X] in
theorem scalingBad_pairwise (e : FailureEvents X) (scaling : Finset X) :
    [e.exclusive.counter,e.exclusive.history,e.exclusive.deadline,e.exclusive.window,
      scalingExclusive e scaling].Pairwise Disjoint := by
  simp [List.pairwise_cons,Finset.disjoint_left,FailureEvents.exclusive,scalingExclusive,
    FailureEvents.mem_bad]
  tauto

/-- Exact symbolic mass only: no numerical estimate for the fifth cell is
asserted or supplied by this theorem. -/
theorem scalingBad_mass (e : FailureEvents X) (scaling : Finset X) (μ : InputLaw X) :
    μ.mass (scalingBad e scaling)=
      ((μ.mass e.exclusive.counter+μ.mass e.exclusive.history)+μ.mass e.exclusive.deadline)+
        μ.mass e.exclusive.window+μ.mass (scalingExclusive e scaling) := by
  rw [scalingBad_partition,FailureEvents.exclusive_bad]
  have add : μ.mass (e.bad∪scalingExclusive e scaling)=μ.mass e.bad+μ.mass (scalingExclusive e scaling) := by
    exact Finset.sum_union (scalingExclusive_disjoint e scaling)
  rw [add,e.mass_exclusive]

end ECDSAAdd.Arithmetic.Paper935
