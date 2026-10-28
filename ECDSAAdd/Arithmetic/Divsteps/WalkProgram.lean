import ECDSAAdd.Framework.Hoare

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Chronological forward schedule; its inverse executes inverse steps in the
opposite chronological order. Each measured step gets its own record slice. -/
def forwardWalk (step : Nat → Program) (start : Nat) : Nat → Program
  | 0 => []
  | n+1 => step start ++ forwardWalk step (start+1) n

def inverseWalk (undo : Nat → Program) (start : Nat) : Nat → Program
  | 0 => []
  | n+1 => inverseWalk undo (start+1) n ++ undo start

theorem forwardWalk_spec (step : Nat → Program) (P : Nat → BasisState → Prop) (limit : Nat)
    (hstep : ∀ i, i<limit → Triple (P i) (step i) (P (i+1))) (start n : Nat)
    (hrange : start+n≤limit) :
    Triple (P start) (forwardWalk step start n) (P (start+n)) := by
  induction n generalizing start with
  | zero => intro s m hs; exact ⟨rfl,hs⟩
  | succ n ih =>
    simpa [forwardWalk,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      (hstep start (by omega)).seq (ih (start+1) (by omega))

/-- Independent forward/inverse records compose through the entire schedule.
The per-step hypotheses will be supplied by physical forward/inverse proofs. -/
theorem inverseWalk_after (step undo : Nat → Program) (P : Nat → BasisState → Prop) (limit : Nat)
    (hstep : ∀ i, i<limit → Triple (P i) (step i) (P (i+1)))
    (hundo : ∀ i, i<limit → ∀ s mf mi, P i s.basis → run (undo i) mi (run (step i) mf s)=s)
    (start n : Nat) (hrange : start+n≤limit) (s : State) (mf mi : List Bool) (hs : P start s.basis) :
    run (inverseWalk undo start n) mi (run (forwardWalk step start n) mf s)=s := by
  induction n generalizing start s mf mi with
  | zero => rfl
  | succ n ih =>
    have ht := (hstep start (by omega) s mf hs).2
    simp only [forwardWalk,inverseWalk,run_append,run_take]
    rw [ih (start+1) (by omega) (run (step start) mf s) _ mi ht]
    exact hundo start (by omega) s mf _ hs

theorem forwardWalk_counts (step : Nat → Program) (T M limit : Nat)
    (hcounts : ∀ i, i<limit → toffoliCount (step i)=T ∧ measurementCount (step i)=M)
    (start n : Nat) (hrange : start+n≤limit) :
    toffoliCount (forwardWalk step start n)=n*T ∧
    measurementCount (forwardWalk step start n)=n*M := by
  induction n generalizing start with
  | zero => simp [forwardWalk,toffoliCount,measurementCount]
  | succ n ih =>
    simp [forwardWalk,toffoliCount_append,measurementCount_append,
      (hcounts start (by omega)).1,(hcounts start (by omega)).2,(ih (start+1) (by omega)).1,(ih (start+1) (by omega)).2,Nat.add_mul,Nat.add_comm]

theorem inverseWalk_counts (undo : Nat → Program) (T M limit : Nat)
    (hcounts : ∀ i, i<limit → toffoliCount (undo i)=T ∧ measurementCount (undo i)=M)
    (start n : Nat) (hrange : start+n≤limit) :
    toffoliCount (inverseWalk undo start n)=n*T ∧
    measurementCount (inverseWalk undo start n)=n*M := by
  induction n generalizing start with
  | zero => simp [inverseWalk,toffoliCount,measurementCount]
  | succ n ih =>
    simp [inverseWalk,toffoliCount_append,measurementCount_append,
      (hcounts start (by omega)).1,(hcounts start (by omega)).2,(ih (start+1) (by omega)).1,(ih (start+1) (by omega)).2,Nat.add_mul]

theorem forwardWalk_wires_subset (step : Nat → Program) (support : Finset Wire) (limit : Nat)
    (hstep : ∀ i, i<limit → wires (step i)⊆support) (start n : Nat)
    (hrange : start+n≤limit) : wires (forwardWalk step start n)⊆support := by
  induction n generalizing start with
  | zero => simp [forwardWalk,wires]
  | succ n ih =>
    rw [forwardWalk,wires_append,Finset.union_subset_iff]
    exact ⟨hstep start (by omega),ih (start+1) (by omega)⟩

theorem inverseWalk_wires_subset (undo : Nat → Program) (support : Finset Wire) (limit : Nat)
    (hstep : ∀ i, i<limit → wires (undo i)⊆support) (start n : Nat)
    (hrange : start+n≤limit) : wires (inverseWalk undo start n)⊆support := by
  induction n generalizing start with
  | zero => simp [inverseWalk,wires]
  | succ n ih =>
    rw [inverseWalk,wires_append,Finset.union_subset_iff]
    exact ⟨ih (start+1) (by omega),hstep start (by omega)⟩

theorem walk_roundTrip (step undo : Nat → Program) (P : Nat → BasisState → Prop) (limit : Nat)
    (hstep : ∀ i, i<limit → Triple (P i) (step i) (P (i+1)))
    (hundo : ∀ i, i<limit → ∀ s mf mi, P i s.basis → run (undo i) mi (run (step i) mf s)=s)
    (start n : Nat) (hrange : start+n≤limit) (s : State) (m : List Bool) (hs : P start s.basis) :
    run (forwardWalk step start n ++ inverseWalk undo start n) m s=s := by
  rw [run_append,run_take]
  exact inverseWalk_after step undo P limit hstep hundo start n hrange s m _ hs

end ECDSAAdd.Arithmetic.Divsteps
