import ECDSAAdd.Arithmetic.Paper935.FreezePin
import ECDSAAdd.Arithmetic.Paper935.History
import ECDSAAdd.Arithmetic.Paper935.HistoryPredicate
import ECDSAAdd.Arithmetic.Paper935.FailureAssembly

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget

/-- Mathematical selector on the post-slot rows and post-slot freeze flag.
The caller binds depth to its physical coefficient-prefix length plus one. -/
def trajectoryStore (tmin depth : Nat) (p x : Int) (t : Nat) : Bool :=
  let u := pinWalk tmin p x (t+1)
  !u.frozen && decide (u.rows.z≤0) && decide ((2:Int)^depth ∣ u.rows.fv)

/-- Unbounded reference stack. No modular truncation can hide a first overflow. -/
def trajectoryHistory (tmin depth : Nat) (p x : Int) : Nat → Nat
  | 0 => 0
  | t+1 => if trajectoryStore tmin depth p x t then
      2*trajectoryHistory tmin depth p x t + (parityControl (pinWalk tmin p x t).rows).toNat
    else trajectoryHistory tmin depth p x t

/-- Exactly the finite push precondition, at every selected stage. Capacity is
an explicit public schedule, not inferred from a sample's largest stack. -/
def HistoryFailure (tmin depth steps : Nat) (capacity : Nat → Nat) (p x : Int) : Prop :=
  ∃ t, t<steps ∧ trajectoryStore tmin depth p x t=true ∧
    ¬(2*trajectoryHistory tmin depth p x t +
      (parityControl (pinWalk tmin p x t).rows).toNat < 2^(capacity t))

theorem no_history_failure_iff (tmin depth steps : Nat) (capacity : Nat → Nat) (p x : Int) :
    ¬HistoryFailure tmin depth steps capacity p x ↔
    ∀ t,t<steps → trajectoryStore tmin depth p x t=true →
      2*trajectoryHistory tmin depth p x t +
        (parityControl (pinWalk tmin p x t).rows).toNat < 2^(capacity t) := by
  simp [HistoryFailure]

/-- Bind the numerical event to the real finite history network's premise. -/
theorem trajectory_push_fit (tmin depth steps : Nat) (capacity : Nat → Nat) (p x : Int)
    (h : ¬HistoryFailure tmin depth steps capacity p x) (t : Nat) (ht : t<steps)
    (store port : Wire) (record : List Wire) (s : BasisState)
    (hs : s store=trajectoryStore tmin depth p x t)
    (hp : s port=parityControl (pinWalk tmin p x t).rows)
    (hr : regValue record s=trajectoryHistory tmin depth p x t)
    (hw : record.length=capacity t) :
    s store=true → 2*regValue record s+(s port).toNat<2^record.length := by
  rw [hs,hp,hr,hw]
  exact (no_history_failure_iff tmin depth steps capacity p x).mp h t ht

/-- The actual push updates to the next unbounded reference value when the
current encoding and selector have been established by the caller. -/
theorem trajectory_push_value (tmin depth steps : Nat) (capacity : Nat → Nat) (p x : Int)
    (h : ¬HistoryFailure tmin depth steps capacity p x) (t : Nat) (ht : t<steps)
    (store port : Wire) (record : List Wire) (s : State) (tape : List Bool)
    (hn : (store::port::record).Nodup)
    (hs : s.basis store=trajectoryStore tmin depth p x t)
    (hp : s.basis port=parityControl (pinWalk tmin p x t).rows)
    (hr : regValue record s.basis=trajectoryHistory tmin depth p x t)
    (hw : record.length=capacity t) :
    regValue record (run (pushHistory store port record) tape s).basis =
      trajectoryHistory tmin depth p x (t+1) := by
  have hf := trajectory_push_fit tmin depth steps capacity p x h t ht store port record s.basis hs hp hr hw
  have run := pushHistory_spec store port record hn s tape hf
  simpa only [trajectoryHistory,hs,hp,hr] using run.2.2.2.1

/-- Include seed representation and every exit, not just the final window. -/
def WindowFailure (tmin : Nat) (exits : List RowWindow) (p x : Int) : Prop :=
  ¬initialWindow.Fits (zSeed p x) ∨
    ExitWindowFailure exits (fun t => (pinWalk tmin p x t).rows)

/-- The signed counter's width includes its sign bit. This is distinct from
freeze offset storage. Every prefix, including the seed, is checked. -/
def CounterFailure (tmin steps width : Nat) (p x : Int) : Prop :=
  ∃ t,t≤steps ∧ ¬PayloadFits (width-1) (pinWalk tmin p x t).rows.z

/-- Conservative deadline category also includes the early-zero exclusion
needed by the existing ideal-walk agreement theorem. -/
def StopFailure (tmin steps : Nat) (p x : Int) : Prop :=
  EarlyZero tmin p x ∨ (pinWalk tmin p x steps).frozen≠true

/-- Use the existing four-category accounting on the SAME original labels.
`input` is the actual arithmetic argument induced by those labels. -/
noncomputable def trajectoryEvents {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (tmin depth steps width : Nat)
    (capacity : Nat → Nat) (exits : List RowWindow) : FailureEvents X := by
  classical
  exact ⟨traceEvent input (CounterFailure tmin steps width p),
    traceEvent input (HistoryFailure tmin depth steps capacity p),
    traceEvent input (StopFailure tmin steps p),
    traceEvent input (WindowFailure tmin exits p)⟩

theorem mem_trajectory_bad {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (tmin depth steps width : Nat)
    (capacity : Nat → Nat) (exits : List RowWindow) (x : X) :
    x∈(trajectoryEvents input p tmin depth steps width capacity exits).bad ↔
    CounterFailure tmin steps width p (input x) ∨
    HistoryFailure tmin depth steps capacity p (input x) ∨
    StopFailure tmin steps p (input x) ∨ WindowFailure tmin exits p (input x) := by
  classical
  simp [FailureEvents.mem_bad,trajectoryEvents,mem_traceEvent]

/-- Outside the declared event, every existing local numerical premise is
available. Gate layouts and actual trace correspondence remain caller duties. -/
theorem trajectory_good {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Int) (tmin depth steps width : Nat)
    (capacity : Nat → Nat) (exits : List RowWindow) (x : X)
    (h : x∉(trajectoryEvents input p tmin depth steps width capacity exits).bad) :
    (∀ t,t≤steps → PayloadFits (width-1) (pinWalk tmin p (input x) t).rows.z) ∧
    (∀ t,t<steps → trajectoryStore tmin depth p (input x) t=true →
      2*trajectoryHistory tmin depth p (input x) t +
        (parityControl (pinWalk tmin p (input x) t).rows).toNat<2^(capacity t)) ∧
    ¬EarlyZero tmin p (input x) ∧ (pinWalk tmin p (input x) steps).frozen=true ∧
    initialWindow.Fits (zSeed p (input x)) ∧
    (∀ (t : Nat) (w : RowWindow),exits[t]?=some w → w.Fits (pinWalk tmin p (input x) (t+1)).rows) := by
  rw [mem_trajectory_bad] at h
  simpa [CounterFailure,HistoryFailure,StopFailure,WindowFailure,ExitWindowFailure,and_assoc] using h

/-- Independent of all termination and counter-success assumptions. -/
noncomputable def offsetOverflowEvent {X : Type*} [Fintype X] (input : X → Int) (p : Int) :
    Finset X := by
  classical
  exact traceEvent input (fun x => ∃ t,t≤authorSteps ∧
    ¬(pinWalk authorFreezeStart p x t).offset<2^6)

theorem offsetOverflowEvent_empty {X : Type*} [Fintype X] (input : X → Int) (p : Int) :
    offsetOverflowEvent input p=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨t,ht,h⟩ := (mem_traceEvent _ _ x).mp hx
  exact h (author_stop_offset_fits p (input x) t ht).2

theorem offsetOverflow_mass_zero {X : Type*} [Fintype X]
    (μ : InputLaw X) (input : X → Int) (p : Int) : μ.mass (offsetOverflowEvent input p)=0 := by
  rw [offsetOverflowEvent_empty,μ.mass_empty]

end ECDSAAdd.Arithmetic.Paper935
