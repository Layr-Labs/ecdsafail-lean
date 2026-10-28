import ECDSAAdd.Arithmetic.Paper935.ArenaCensus

namespace ECDSAAdd.Arithmetic.Paper935

/-- Release samples are supplied boundary states. Their correspondence to a
program's actual execution is a separate obligation, not checked by this log. -/
inductive ArenaLogAction where
  | reserve (wires : Finset Wire)
  | release (wires : Finset Wire) (sample : BasisState)

def ArenaLogAction.execute (action : ArenaLogAction) (A : Arena) : Option Arena :=
  match action with
  | .reserve qs => A.reserve qs
  | .release qs s => A.release qs s

/-- Regenerate every intermediate live set; fail at the first invalid action.
The initial and terminal snapshots are both retained. -/
def checkArenaLog (A : Arena) : List ArenaLogAction → Option (List Arena)
  | [] => some [A]
  | action::actions => do
    let B ← action.execute A
    let rest ← checkArenaLog B actions
    pure (A::rest)

/-- Every adjacent transition is the existing allocator's successful result.
This relation does not assume an arbitrary supplied census is valid. -/
inductive ValidArenaLog : Arena → List ArenaLogAction → List Arena → Prop where
  | nil (A : Arena) : ValidArenaLog A [] [A]
  | cons (A B : Arena) (action : ArenaLogAction) (actions : List ArenaLogAction)
      (trace : List Arena) (step : action.execute A=some B)
      (rest : ValidArenaLog B actions trace) :
      ValidArenaLog A (action::actions) (A::trace)

theorem checkArenaLog_sound (A : Arena) (actions : List ArenaLogAction) (trace : List Arena)
    (accepted : checkArenaLog A actions=some trace) : ValidArenaLog A actions trace := by
  induction actions generalizing A trace with
  | nil =>
    simp only [checkArenaLog,Option.some.injEq] at accepted
    subst trace
    exact .nil A
  | cons action actions ih =>
    cases step : action.execute A with
    | none => simp [checkArenaLog,step] at accepted
    | some B =>
      cases tail : checkArenaLog B actions with
      | none => simp [checkArenaLog,step,tail] at accepted
      | some rest =>
        simp [checkArenaLog,step,tail] at accepted
        subst trace
        exact .cons A B action actions rest step (ih B rest tail)

theorem checkArenaLog_complete (A : Arena) (actions : List ArenaLogAction) (trace : List Arena)
    (valid : ValidArenaLog A actions trace) : checkArenaLog A actions=some trace := by
  induction valid with
  | nil A => rfl
  | cons A B action actions trace step rest ih => simp [checkArenaLog,step,ih]

theorem checkArenaLog_iff (A : Arena) (actions : List ArenaLogAction) (trace : List Arena) :
    checkArenaLog A actions=some trace ↔ ValidArenaLog A actions trace :=
  ⟨checkArenaLog_sound A actions trace,checkArenaLog_complete A actions trace⟩

theorem ValidArenaLog.length (A : Arena) (actions : List ArenaLogAction) (trace : List Arena)
    (valid : ValidArenaLog A actions trace) : trace.length=actions.length+1 := by
  induction valid with
  | nil A => rfl
  | cons A B action actions trace step rest ih => simp [ih]

/-- The checker computes peak occupancy only after validating every allocator
transition. A successful result is not a certificate of source-log completeness. -/
def checkedArenaPeak (A : Arena) (actions : List ArenaLogAction) : Option Nat :=
  (checkArenaLog A actions).map (fun trace => livePeak (trace.map Arena.live))

theorem checkedArenaPeak_exact (A : Arena) (actions : List ArenaLogAction) (trace : List Arena)
    (accepted : checkArenaLog A actions=some trace) :
    checkedArenaPeak A actions=some (livePeak (trace.map Arena.live)) := by
  simp [checkedArenaPeak,accepted]

theorem checkedArenaPeak_sound (A : Arena) (actions : List ArenaLogAction) (peak : Nat)
    (accepted : checkedArenaPeak A actions=some peak) :
    ∃trace,ValidArenaLog A actions trace ∧ trace.length=actions.length+1 ∧
      peak=livePeak (trace.map Arena.live) := by
  cases result : checkArenaLog A actions with
  | none => simp [checkedArenaPeak,result] at accepted
  | some trace =>
    have valid := checkArenaLog_sound A actions trace result
    have eq : livePeak (trace.map Arena.live)=peak := by
      simpa [checkedArenaPeak,result] using accepted
    exact ⟨trace,valid,valid.length A actions trace,eq.symm⟩

/-- Exact bound on every generated snapshot, for any requested budget. -/
theorem checkedArenaPeak_bound (A : Arena) (actions : List ArenaLogAction) (trace : List Arena)
    (accepted : checkArenaLog A actions=some trace) (budget : Nat) :
    (∃peak,checkedArenaPeak A actions=some peak ∧ peak≤budget) ↔
      ∀B∈trace,B.live.card≤budget := by
  rw [checkedArenaPeak_exact A actions trace accepted]
  simp [livePeak_le_iff]

/-- Successful log reservations cannot overlap already live wires. -/
theorem arenaLog_reserve_valid (A B : Arena) (qs : Finset Wire)
    (accepted : (ArenaLogAction.reserve qs).execute A=some B) :
    qs⊆arenaWires ∧ Disjoint A.live qs :=
  (A.reserve_success qs).mp ⟨B,accepted⟩

/-- Release validates ownership and zeroes in the supplied state; a caller
must separately identify that sample with the real program boundary. -/
theorem arenaLog_release_valid (A B : Arena) (qs : Finset Wire) (s : BasisState)
    (accepted : (ArenaLogAction.release qs s).execute A=some B) :
    qs⊆A.live ∧ ∀q∈qs,s q=false :=
  (A.release_success qs s).mp ⟨B,accepted⟩

-- The peak includes an interior reservation even after later release.
example : checkedArenaPeak ⟨∅,Finset.empty_subset _⟩
    [.reserve {0,1},.release {0,1} (fun _ => false)] = some 2 := by decide +kernel

-- Reusing a live wire is rejected rather than counted twice.
example : checkedArenaPeak ⟨∅,Finset.empty_subset _⟩
    [.reserve {0},.reserve {0}] = none := by decide +kernel

-- A dirty release sample is rejected rather than interpreted as a reset.
example : checkedArenaPeak ⟨∅,Finset.empty_subset _⟩
    [.reserve {0},.release {0} (fun _ => true)] = none := by decide +kernel

end ECDSAAdd.Arithmetic.Paper935
