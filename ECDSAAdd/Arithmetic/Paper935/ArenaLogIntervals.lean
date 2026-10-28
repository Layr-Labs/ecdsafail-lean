import ECDSAAdd.Arithmetic.Paper935.ArenaLog

namespace ECDSAAdd.Arithmetic.Paper935

/-- The source exporter uses half-open [lo,hi) intervals. Decode to sets, so
adjacent or overlapping intervals never inflate occupancy by double-counting. -/
def arenaIntervalSet : List (Nat × Nat) → Finset Wire
  | [] => ∅
  | (lo,hi)::rs => Finset.Ico lo hi ∪ arenaIntervalSet rs

theorem arenaIntervalSet_mem (rs : List (Nat × Nat)) (q : Wire) :
    q∈arenaIntervalSet rs ↔ ∃r∈rs,r.1≤q ∧ q<r.2 := by
  induction rs with
  | nil => simp [arenaIntervalSet]
  | cons r rs ih => simp [arenaIntervalSet,ih]

/-- Boundary adapter only: the existing allocator checker still validates all
interior actions. No endpoint-only peak estimate or new allocator is used. -/
def checkArenaStage (A : Arena) (before after : List (Nat × Nat))
    (actions : List ArenaLogAction) : Option (List Arena) :=
  if A.live=arenaIntervalSet before then do
    let trace ← checkArenaLog A actions
    if trace.getLast?.map Arena.live=some (arenaIntervalSet after) then some trace else none
  else none

theorem checkArenaStage_sound (A : Arena) (before after : List (Nat × Nat))
    (actions : List ArenaLogAction) (trace : List Arena)
    (accepted : checkArenaStage A before after actions=some trace) :
    A.live=arenaIntervalSet before ∧ ValidArenaLog A actions trace ∧
      trace.length=actions.length+1 ∧
      trace.getLast?.map Arena.live=some (arenaIntervalSet after) := by
  unfold checkArenaStage at accepted
  split at accepted
  next start =>
    cases result : checkArenaLog A actions with
    | none => simp [result] at accepted
    | some generated =>
      simp only [result] at accepted
      change (if generated.getLast?.map Arena.live=some (arenaIntervalSet after)
        then some generated else none)=some trace at accepted
      split at accepted
      next finish =>
        cases Option.some.inj accepted
        have valid := checkArenaLog_sound A actions trace result
        exact ⟨start,valid,valid.length A actions trace,finish⟩
      next => simp at accepted
  next => simp at accepted

theorem checkArenaStage_complete (A : Arena) (before after : List (Nat × Nat))
    (actions : List ArenaLogAction) (trace : List Arena)
    (start : A.live=arenaIntervalSet before)
    (valid : ValidArenaLog A actions trace)
    (finish : trace.getLast?.map Arena.live=some (arenaIntervalSet after)) :
    checkArenaStage A before after actions=some trace := by
  unfold checkArenaStage
  rw [if_pos start,checkArenaLog_complete A actions trace valid]
  change (if trace.getLast?.map Arena.live=some (arenaIntervalSet after)
    then some trace else none)=some trace
  rw [if_pos finish]

def checkedArenaStagePeak (A : Arena) (before after : List (Nat × Nat))
    (actions : List ArenaLogAction) : Option Nat :=
  (checkArenaStage A before after actions).map (fun trace => livePeak (trace.map Arena.live))

theorem checkedArenaStagePeak_sound (A : Arena) (before after : List (Nat × Nat))
    (actions : List ArenaLogAction) (peak : Nat)
    (accepted : checkedArenaStagePeak A before after actions=some peak) :
    ∃trace,A.live=arenaIntervalSet before ∧ ValidArenaLog A actions trace ∧
      trace.length=actions.length+1 ∧
      trace.getLast?.map Arena.live=some (arenaIntervalSet after) ∧
      peak=livePeak (trace.map Arena.live) := by
  cases result : checkArenaStage A before after actions with
  | none => simp [checkedArenaStagePeak,result] at accepted
  | some trace =>
    have h := checkArenaStage_sound A before after actions trace result
    have eq : livePeak (trace.map Arena.live)=peak := by
      simpa [checkedArenaStagePeak,result] using accepted
    exact ⟨trace,h.1,h.2.1,h.2.2.1,h.2.2.2,eq.symm⟩

-- Empty endpoints do not hide the internal two-wire peak.
example : checkedArenaStagePeak ⟨∅,Finset.empty_subset _⟩ [] []
    [.reserve {0,1},.release {0,1} (fun _ => false)] = some 2 := by decide +kernel

-- The interval [0,1) contains 0 but not 1; mismatching the actual final set fails.
example : checkedArenaStagePeak ⟨∅,Finset.empty_subset _⟩ [] [(0,1)]
    [.reserve {0,1}] = none := by decide +kernel

example : arenaIntervalSet [(0,2),(1,3)]=({0,1,2} : Finset Wire) := by decide +kernel

end ECDSAAdd.Arithmetic.Paper935
