import ECDSAAdd.Arithmetic.Paper935.Fold32Roundtrip

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def fold32PlacedReduce (f : Wire → Wire) : Program := renameProgram f fold32Reduce
def fold32PlacedUnreduce (f : Wire → Wire) : Program := renameProgram f fold32Unreduce

def Fold32PlacedReady (f : Wire → Wire) (s : BasisState) : Prop :=
  ∀ i<32,s (f (258+i))=false

private theorem pull_word (r : List Wire) (f : Wire → Wire) (s : State) :
    regValue r (pullState f s).basis=regValue (r.map f) s.basis := by
  induction r with
  | nil => rfl
  | cons q rest ih =>
    change (if s.basis (f q) then 1 else 0)+2*regValue rest (pullState f s).basis=
      (if s.basis (f q) then 1 else 0)+2*regValue (rest.map f) s.basis
    rw [ih]

private theorem pull_ready (f : Wire → Wire) (s : State) :
    Fold32Ready 0 (pullState f s).basis ↔ Fold32PlacedReady f s.basis := by
  constructor
  · intro h i hi
    exact h i hi (Nat.zero_le _)
  · intro h i hi _
    exact h i hi

attribute [local irreducible] fold32Reduce fold32Unreduce

theorem fold32PlacedReduce_contract (f : Wire → Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (ready : Fold32PlacedReady f s.basis)
    (enabled : s.basis (f 0)=true) (flag : s.basis (f 290)=false)
    (bound : regValue (fold32Word.map f) s.basis<2*fold32Prime) :
    let out := run (fold32PlacedReduce f) m s
    regValue (fold32Word.map f) out.basis=regValue (fold32Word.map f) s.basis%fold32Prime ∧
    Fold32PlacedReady f out.basis ∧ out.basis (f 290)=decide (regValue (fold32Word.map f) s.basis<fold32Prime) ∧
    out.basis (f 0)=true ∧ out.phase=s.phase := by
  have h := fold32Reduce_contract (pullState f s) m ((pull_ready f s).mpr ready) enabled flag
    (by rwa [pull_word])
  have c := fold32Reduce_control (pullState f s) m ((pull_ready f s).mpr ready)
  have execution := run_rename f hf fold32Reduce m s
  dsimp only at h
  rw [←execution,pull_word,pull_word,pull_ready] at h
  rw [←execution] at c
  exact ⟨h.1,h.2.1,h.2.2.1,c.trans enabled,h.2.2.2⟩

theorem fold32PlacedUnreduce_contract (f : Wire → Wire) (hf : Function.Injective f)
    (s : State) (m : List Bool) (ready : Fold32PlacedReady f s.basis)
    (enabled : s.basis (f 0)=true) (bound : regValue (fold32Word.map f) s.basis<fold32Prime) :
    let out := run (fold32PlacedUnreduce f) m s
    regValue (fold32Word.map f) out.basis=regValue (fold32Word.map f) s.basis+
      (if s.basis (f 290) then 0 else fold32Prime) ∧
    Fold32PlacedReady f out.basis ∧ out.basis (f 290)=false ∧ out.basis (f 0)=true ∧ out.phase=s.phase := by
  have h := fold32Unreduce_contract (pullState f s) m ((pull_ready f s).mpr ready) enabled
    (by rwa [pull_word])
  have execution := run_rename f hf fold32Unreduce m s
  dsimp only at h
  rw [←execution,pull_word,pull_word,pull_ready] at h
  exact h

/-- All mapped source states return to their original values, even if the
injective placement is not surjective onto the ambient wire space. -/
theorem fold32Placed_roundtrip_pull (f : Wire → Wire) (hf : Function.Injective f)
    (s : State) (m n : List Bool) (ready : Fold32PlacedReady f s.basis)
    (enabled : s.basis (f 0)=true) (flag : s.basis (f 290)=false)
    (bound : regValue (fold32Word.map f) s.basis<2*fold32Prime) :
    pullState f (run (fold32PlacedUnreduce f) n (run (fold32PlacedReduce f) m s))=pullState f s := by
  rw [fold32PlacedUnreduce,run_rename f hf,fold32PlacedReduce,run_rename f hf]
  exact fold32Reduce_roundtrip (pullState f s) m n ((pull_ready f s).mpr ready) enabled flag
    (by rwa [pull_word])

end ECDSAAdd.Arithmetic.Paper935
