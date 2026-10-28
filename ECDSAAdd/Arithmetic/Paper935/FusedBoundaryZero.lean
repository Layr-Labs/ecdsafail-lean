import ECDSAAdd.Arithmetic.Paper935.FusedBoundaryLayout
import ECDSAAdd.Arithmetic.Paper935.OwnedHostSupport
import ECDSAAdd.Arithmetic.Paper935.EndpointSlotAssembly

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Divsteps FailureBudget
attribute [local irreducible] seededAuthorWalkProgram seededAuthorWalkReverse closerProgram

/-- The owned A word is not inferred clean from allocator readiness. Its
initial zero value is transported through the actual seed/walk/closer. -/
theorem fusedClosed_aHost_zero (p ordinal : Nat) (slots : List HistoricalSlot)
    (compiled : compileAuthorWalk=some slots) (s : State) (m : List Bool)
    (initial : ∀q∈aHost,s.basis q=false) :
    ∀q∈aHost,(endpointClosed p ordinal slots m s).basis q=false := by
  intro q hq
  have dis := authorWalk_aHost_support p ordinal slots compiled
  have away : q∉recordedWires (seededAuthorWalkProgram p slots ++
      embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p)) := by
    intro hh
    apply Finset.disjoint_left.mp dis hq
    simp only [recordedWires_append,Finset.mem_union] at hh ⊢
    rcases hh with h|h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
  have frame := runWithTape_preserves_outside
    (seededAuthorWalkProgram p slots ++ embedRecorded (closerProgram (walkExitBank walkSeedBank slots) p))
    m ordinal s q away
  simpa only [runWithTape_append,runWithTape_embedRecorded,endpointClosed,endpointCursor] using
    frame.trans (initial q hq)

/-- The actual successful closer supplies readiness for the selected pool;
its bits are zero by reservation, not by a new numeric success predicate. -/
theorem fusedClosed_pool_zero {X : Type*} [Fintype X] [DecidableEq X]
    (input : X → Int) (p : Nat) (hp : p<2^256) (x : X) (odd : (p : Int)%2=1)
    (coprime : Int.gcd p (input x)=1) (good : x∉(authorTrajectoryEvents input p).bad)
    (slots : List HistoricalSlot) (compiled : compileAuthorWalk=some slots)
    (s : State) (m : List Bool) (ordinal : Nat) (ready : seedBefore.Ready s.basis)
    (encoding : (regValue seedG s.basis : Int)=input x)
    (B : Arena) (pool : List Wire)
    (allocated : (authorClosedArena slots).borrowMany 24=some (B,pool)) :
    pool.length=24 ∧ (∀q∈pool,(endpointClosed p ordinal slots m s).basis q=false) ∧
      B.Ready (endpointClosed p ordinal slots m s).basis := by
  have closed := seededAuthorWalk_closer_release input p hp x odd coprime good slots compiled
    s m (m.drop (endpointCursor p ordinal slots)) ordinal ready encoding
  exact fusedPool_zero _ B pool _ closed.2.1 allocated

/-- HMR demolition clears the borrowed word for every tape, but its phase
is deliberately not claimed restored: later replay must discharge that debt. -/
def fusedDemolish (word : List Wire) : Program := word.map (fun q => .measureX q [] [])

theorem fusedDemolish_basis (word : List Wire) (s : State) (m : List Bool) :
    ∀q,(run (fusedDemolish word) m s).basis q=if q∈word then false else s.basis q := by
  induction word generalizing s m with
  | nil => intro q; simp [fusedDemolish,run]
  | cons w ws ih =>
    intro q
    simp only [fusedDemolish,List.map_cons,run]
    change (run (fusedDemolish ws) m.tail (measureAndCorrect w [] [] (m.headD false) s)).basis q = _
    rw [ih]
    by_cases hq : q∈ws
    · simp [hq]
    · by_cases eq : q=w
      · subst q; simp [hq,measureAndCorrect,correct,writeBit]
      · simp [hq,eq,measureAndCorrect,correct,writeBit]

theorem fusedDemolish_zero (word : List Wire) (s : State) (m : List Bool) :
    ∀q∈word,(run (fusedDemolish word) m s).basis q=false := by
  intro q hq
  simp [fusedDemolish_basis,hq]

theorem fusedDemolish_recorded_zero (word : List Wire) (s : State)
    (m : List Bool) (ordinal : Nat) :
    ∀q∈word,(runWithTape (embedRecorded (fusedDemolish word)) m ordinal s).basis q=false := by
  rw [runWithTape_embedRecorded]
  exact fusedDemolish_zero word s (m.drop ordinal)

/-- The s2 unpark boundary may move the demolished multiplicand view;
physical zeroes follow those same moves, without discarding its phase. -/
theorem fusedDemolish_repack_zero (word : List Wire) (s : State)
    (m n : List Bool) (ms : List (Wire × Wire)) (valid : ∀p∈ms,p.1≠p.2) :
    ∀q∈repackView ms word,
      (run (repack ms) n (run (fusedDemolish word) m s)).basis q=false :=
  repack_zero ms valid word _ n (fusedDemolish_zero word s m)

end ECDSAAdd.Arithmetic.Paper935
