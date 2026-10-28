import ECDSAAdd.Arithmetic.Paper935.CarryAdder

namespace ECDSAAdd.Arithmetic.Paper935

/-- Physical addresses include both point coordinates, the third word and all
transient wires. There is no auxiliary arena outside these 935 addresses. -/
def arenaWires : Finset Wire := Finset.range 935

def xHost : Finset Wire := Finset.Ico 0 256
def yHost : Finset Wire := Finset.Ico 256 512
def aHost : Finset Wire := Finset.Ico 512 768

structure Arena where
  live : Finset Wire
  bounded : live⊆arenaWires

/-- Only clean, unowned wires may be borrowed by a subsequent stage. -/
def Arena.Ready (A : Arena) (s : BasisState) : Prop :=
  ∀ q∈arenaWires,q∉A.live → s q=false

/-- Exhaustion and overlapping claims are explicit failures. They neither
silently grow the arena nor overwrite a live register. -/
def Arena.reserve (A : Arena) (qs : Finset Wire) : Option Arena :=
  if h : qs⊆arenaWires ∧ Disjoint A.live qs then
    some ⟨A.live∪qs,Finset.union_subset A.bounded h.1⟩
  else none

/-- Release is a permission check, not a quantum reset. A dirty wire cannot
be returned to the allocator. The caller must prove its cleaning circuit. -/
def Arena.release (A : Arena) (qs : Finset Wire) (s : BasisState) : Option Arena :=
  if qs⊆A.live ∧ ∀ q∈qs,s q=false then
    some ⟨A.live\qs,Finset.Subset.trans Finset.sdiff_subset A.bounded⟩
  else none

theorem Arena.peak_bound (A : Arena) : A.live.card≤935 := by
  simpa [arenaWires] using Finset.card_le_card A.bounded

theorem Arena.reserve_success (A : Arena) (qs : Finset Wire) :
    (∃ B,A.reserve qs=some B) ↔ qs⊆arenaWires ∧ Disjoint A.live qs := by
  unfold reserve
  split <;> simp_all

theorem Arena.reserve_ready (A B : Arena) (qs : Finset Wire) (s : BasisState)
    (ha : A.Ready s) (h : A.reserve qs=some B) :
    B.Ready s ∧ (∀ q∈qs,s q=false) := by
  unfold reserve at h
  split at h
  next hv =>
    cases h
    constructor
    · intro q hq hnot
      exact ha q hq (fun hm => hnot (Finset.mem_union_left _ hm))
    · intro q hq
      exact ha q (hv.1 hq) (fun hl => Finset.disjoint_left.mp hv.2 hl hq)
  next hv => simp at h

theorem Arena.release_success (A : Arena) (qs : Finset Wire) (s : BasisState) :
    (∃ B,A.release qs s=some B) ↔ qs⊆A.live ∧ ∀ q∈qs,s q=false := by
  unfold release
  split <;> simp_all

theorem Arena.release_ready (A B : Arena) (qs : Finset Wire) (s : BasisState)
    (ha : A.Ready s) (h : A.release qs s=some B) : B.Ready s := by
  unfold release at h
  split at h
  next hv =>
    cases h
    intro q hq hn
    by_cases hmem : q∈qs
    · exact hv.2 q hmem
    · exact ha q hq (fun hl => hn (Finset.mem_sdiff.mpr ⟨hl,hmem⟩))
  next hv => simp at h

/-- A composed program uses the same arena, even when its stages reuse wires. -/
theorem arena_append (p q : Program) (hp : wires p⊆arenaWires) (hq : wires q⊆arenaWires) :
    wires (p++q)⊆arenaWires := by
  rw [wires_append]
  exact Finset.union_subset hp hq

theorem arena_program_qubits (p : Program) (h : wires p⊆arenaWires) : qubitCount p≤935 := by
  simpa [arenaWires] using Finset.card_le_card h

/-- The three main words alone consume 768 addresses; the remaining 167
addresses are shared by signs, counters, history, spills and arithmetic. -/
theorem hosts_partition : xHost∪yHost∪aHost=Finset.range 768 := by
  unfold xHost yHost aHost
  rw [Finset.Ico_union_Ico_eq_Ico (by decide) (by decide),
    Finset.Ico_union_Ico_eq_Ico (by decide) (by decide)]
  exact congrFun Nat.Ico_zero_eq_range 768

theorem hosts_capacity : (xHost∪yHost∪aHost).card=768 ∧
    (arenaWires\(xHost∪yHost∪aHost)).card=167 := by
  rw [hosts_partition]
  constructor
  · simp
  · rw [Finset.card_sdiff_of_subset (by intro q hq; simp [arenaWires] at hq ⊢; omega)]
    simp [arenaWires]

/-- Concrete wiring for a row adder must stay in the shared arena. -/
theorem rowAdd_in_arena (c k : Wire) (a b : List Wire)
    (h : (c::k::(a++b)).toFinset⊆arenaWires) :
    wires (rowAdd c a b k)⊆arenaWires := (rowAdd_support c k a b).trans h

/-- A stage declares which live wires it may overwrite. Read-only hosts may
be in program support, but their restoration is a semantic obligation. -/
structure StageContract where
  before : Arena
  during : Arena
  after : Arena
  borrowed : Finset Wire
  released : Finset Wire
  writable : Finset Wire
  program : Program
  reserve_ok : before.reserve borrowed = some during
  writable_live : writable ⊆ during.live
  support_live : wires program ⊆ during.live
  precondition : State → Prop
  frame : ∀ s m, precondition s → before.Ready s.basis →
    ∀ q, q ∉ writable → (run program m s).basis q = s.basis q
  release_ok : ∀ s m, precondition s → before.Ready s.basis →
    during.release released (run program m s).basis = some after

/-- Cleaning and frame obligations give the next stage a ready arena. No
phase-preservation assumption is hidden in this storage contract. -/
theorem StageContract.ready_after (C : StageContract) (s : State) (m : List Bool)
    (hp : C.precondition s) (hr : C.before.Ready s.basis) :
    C.after.Ready (run C.program m s).basis := by
  apply Arena.release_ready C.during C.after C.released _ _ (C.release_ok s m hp hr)
  intro q hq hn
  rw [run_preserves_outside C.program m s q (fun h => hn (C.support_live h))]
  exact (Arena.reserve_ready C.before C.during C.borrowed s.basis hr C.reserve_ok).1 q hq hn

theorem StageContract.peak (C : StageContract) :
    C.before.live.card ≤ 935 ∧ C.during.live.card ≤ 935 ∧ C.after.live.card ≤ 935 :=
  ⟨C.before.peak_bound,C.during.peak_bound,C.after.peak_bound⟩

/-- This bounds every declared live set in a finite schedule, not just the
union of wires touched by one arithmetic block. Instantiating the schedule
with the complete point-add circuit remains a separate obligation. -/
theorem schedule_peak (schedule : List Arena) :
    ∀ A ∈ schedule, A.live.card ≤ 935 := by
  intro A _
  exact A.peak_bound

end ECDSAAdd.Arithmetic.Paper935
