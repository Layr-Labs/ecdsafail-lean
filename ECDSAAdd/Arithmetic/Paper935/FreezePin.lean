import ECDSAAdd.Arithmetic.Paper935.AuthorSchedule

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps

/-- Integer-level control state, before proving the actual gate execution.
The record is an offset from the public freeze-start dial; zero means unset. -/
structure PinState where
  rows : ZState
  frozen : Bool
  offset : Nat

/-- Active arithmetic precedes the armed post-step zero test (F7). Before
Tmin there is no test, even if g has already become zero. -/
def pinStep (tmin t : Nat) (u : PinState) : PinState :=
  if u.frozen then u else
    let next := zStep u.rows
    if tmin≤t ∧ next.g=0 then ⟨next,true,t+1-tmin⟩ else ⟨next,false,0⟩

def pinWalk (tmin : Nat) (p x : Int) : Nat → PinState
  | 0 => ⟨zSeed p x,false,0⟩
  | t+1 => pinStep tmin t (pinWalk tmin p x t)

/-- A first zero at or before Tmin escapes the omitted tests. In particular
zero input is excluded by the successful-lane bridge, rather than silently
being treated as an invertible input. -/
def EarlyZero (tmin : Nat) (p x : Int) : Prop :=
  ∃ t,t≤tmin ∧ (zWalk p x t).g=0

theorem no_early_zero_iff (tmin : Nat) (p x : Int) :
    ¬EarlyZero tmin p x ↔ ∀ t,t≤tmin → (zWalk p x t).g≠0 := by
  simp [EarlyZero]

theorem pinStep_frozen (tmin t : Nat) (u : PinState) (h : u.frozen=true) :
    pinStep tmin t u=u := by simp [pinStep,h]

/-- No early escape suffices for agreement of all five integer fields and
for the physical-control model's flag to match ideal g=0. This is not yet
a theorem about the compiled quantum circuit or measured records. -/
theorem pinWalk_agrees (tmin : Nat) (p x : Int) (h : ¬EarlyZero tmin p x) (t : Nat) :
    (pinWalk tmin p x t).rows=zWalk p x t ∧
      (pinWalk tmin p x t).frozen=decide ((zWalk p x t).g=0) := by
  have he := (no_early_zero_iff tmin p x).mp h
  induction t with
  | zero =>
    have hz := he 0 (Nat.zero_le _)
    change (zSeed p x).g≠0 at hz
    simp [pinWalk,zWalk,hz]
  | succ t ih =>
    by_cases hz : (zWalk p x t).g=0
    · have hf : (pinWalk tmin p x t).frozen=true := by simpa [hz] using ih.2
      simp [pinWalk,pinStep,hf,zWalk_succ,hz,ih.1]
    · have hf : (pinWalk tmin p x t).frozen=false := by simpa [hz] using ih.2
      by_cases ht : tmin≤t
      · by_cases hn : (zStep (zWalk p x t)).g=0 <;>
          simp [pinWalk,pinStep,hf,ih.1,ht,hn,zWalk_succ,hz]
      · have hn : (zStep (zWalk p x t)).g≠0 := by
          have hh := he (t+1) (by omega)
          simpa only [zWalk_succ,if_neg hz] using hh
        simp [pinWalk,pinStep,hf,ih.1,ht,hn,zWalk_succ,hz]

/-- The offset is bounded purely by the armed schedule length. No assertion
about z's six-bit range or successful termination is used. -/
def PinState.RecordValid (tmin t : Nat) (u : PinState) : Prop :=
  (u.frozen=true ↔ 0<u.offset) ∧ u.offset≤t-tmin

theorem pinStep_record (tmin t : Nat) (u : PinState) (h : u.RecordValid tmin t) :
    (pinStep tmin t u).RecordValid tmin (t+1) := by
  cases hf : u.frozen with
  | true =>
    rw [pinStep_frozen tmin t u hf]
    exact ⟨h.1,by have hb := h.2; omega⟩
  | false =>
    unfold pinStep
    simp only [hf,Bool.false_eq_true,ite_false]
    split
    next hh =>
      simp only [PinState.RecordValid,true_iff]
      constructor
      · omega
      · exact Nat.le_refl _
    next hh => simp [PinState.RecordValid]

theorem pinWalk_record (tmin : Nat) (p x : Int) (t : Nat) :
    (pinWalk tmin p x t).RecordValid tmin t := by
  induction t with
  | zero => simp [pinWalk,PinState.RecordValid]
  | succ t ih => exact pinStep_record tmin t _ ih

theorem pinWalk_frozen_tail (tmin : Nat) (p x : Int) (t k : Nat)
    (h : (pinWalk tmin p x t).frozen=true) :
    pinWalk tmin p x (t+k)=pinWalk tmin p x t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.add_succ,pinWalk,ih]
    exact pinStep_frozen tmin (t+k) _ h

/-- On the first successful armed detection, the newly written record is
exactly the step's offset. A pre-existing frozen record is never rewritten. -/
theorem pinStep_fire (tmin t : Nat) (u : PinState) (hf : u.frozen=false)
    (ht : tmin≤t) (hz : (zStep u.rows).g=0) :
    (pinStep tmin t u).frozen=true ∧ (pinStep tmin t u).offset=t+1-tmin := by
  simp [pinStep,hf,ht,hz]

/-- At the first ideal zero after a nonzero state, the omitted-detection
model records the same stopping step with the required offset. -/
theorem pinWalk_first_zero (tmin : Nat) (p x : Int) (h : ¬EarlyZero tmin p x)
    (t : Nat) (hprev : (zWalk p x t).g≠0) (hnext : (zWalk p x (t+1)).g=0) :
    (pinWalk tmin p x (t+1)).frozen=true ∧
      (pinWalk tmin p x (t+1)).offset=t+1-tmin := by
  have ht : tmin≤t := by
    by_contra hn
    exact ((no_early_zero_iff tmin p x).mp h (t+1) (by omega)) hnext
  have ha := pinWalk_agrees tmin p x h t
  have hf : (pinWalk tmin p x t).frozen=false := by simpa [hprev] using ha.2
  have hz : (zStep (pinWalk tmin p x t).rows).g=0 := by
    rw [ha.1]
    simpa only [zWalk_succ,if_neg hprev] using hnext
  exact pinStep_fire tmin t _ hf ht hz

/-- The early-zero exclusion is substantive: with zero input the undetected
first step increments z, whereas the ideal walk is already frozen. -/
theorem pin_zero_counterexample :
    (pinWalk 498 17 0 1).rows.z=1 ∧ (zWalk 17 0 1).z=0 := by decide

/-- For all prefixes of the 533-step schedule, the stop offset fits six bits.
This is the freeze record width, not the unrelated six-bit z counter. -/
theorem author_stop_offset_fits (p x : Int) (t : Nat) (ht : t≤authorSteps) :
    (pinWalk authorFreezeStart p x t).offset≤35 ∧
      (pinWalk authorFreezeStart p x t).offset<2^6 := by
  have hb := (pinWalk_record authorFreezeStart p x t).2
  simp only [authorSteps] at ht
  simp only [authorFreezeStart] at hb ⊢
  constructor <;> omega

/-- The numeric exit-window event can now be transported to the pinned
integer model under an explicit no-early-zero premise. -/
theorem pin_exit_failure_iff (tmin : Nat) (p x : Int) (h : ¬EarlyZero tmin p x)
    (exits : List RowWindow) :
    ExitWindowFailure exits (fun t => (pinWalk tmin p x t).rows) ↔
      ExitWindowFailure exits (zWalk p x) := by
  have he : (fun t => (pinWalk tmin p x t).rows)=zWalk p x := by
    funext t
    exact (pinWalk_agrees tmin p x h t).1
  rw [he]

end ECDSAAdd.Arithmetic.Paper935
