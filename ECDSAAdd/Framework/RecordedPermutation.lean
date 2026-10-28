import ECDSAAdd.Framework.FiniteWirePermutation

namespace ECDSAAdd

theorem renameRecorded_wellFormed (f : Wire → Wire) (p : RecordedProgram) (k : Nat) :
    RecordedWellFormedAt k (renameRecordedProgram f p) ↔ RecordedWellFormedAt k p := by
  induction p generalizing k with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | gate i =>
      have count := (renameProgram_counts f [i]).2
      simp only [renameProgram,List.map_cons,List.map_nil] at count
      simpa only [renameRecordedProgram,List.map_cons,renameRecordedInstr,RecordedWellFormedAt,count] using ih (k+measurementCount [i])
    | phaseFromRecord j cs =>
      change (j<k ∧ RecordedWellFormedAt k (renameRecordedProgram f p)) ↔ (j<k ∧ RecordedWellFormedAt k p)
      exact and_congr_right (fun _ => ih k)

theorem renameRecorded_append (f : Wire → Wire) (p q : RecordedProgram) :
    renameRecordedProgram f (p++q)=renameRecordedProgram f p++renameRecordedProgram f q := List.map_append

theorem renameRecorded_embed (f : Wire → Wire) (p : Program) :
    renameRecordedProgram f (embedRecorded p)=embedRecorded (renameProgram f p) := by
  induction p with
  | nil => rfl
  | cons i p ih => simpa only [renameRecordedProgram,embedRecorded,renameProgram,List.map_cons,renameRecordedInstr] using congrArg (List.cons (.gate (renameInstr f i))) ih

theorem runRecorded_rename_cursor (f : Wire → Wire) (p : RecordedProgram) (ctx : RecordedContext) (s : State) :
    (runRecorded (renameRecordedProgram f p) ctx s).2= (runRecorded p ctx s).2 := by
  simp only [runRecorded,(renameRecorded_counts f p).2]

theorem runWithTape_permutation_restore (e : Equiv.Perm Wire) (p : RecordedProgram)
    (m : List Bool) (k : Nat) (s : State)
    (restored : runWithTape p m k (pullState e s)=pullState e s) :
    runWithTape (renameRecordedProgram e p) m k s=s := by
  apply pullState_equiv_injective e
  rw [runWithTape_rename e e.injective,restored]

theorem runWithTape_permutation_output (e : Equiv.Perm Wire) (p : RecordedProgram)
    (O : Finset Wire) (v : BasisState) (m : List Bool) (k : Nat) (s : State)
    (output : runWithTape p m k (pullState e s)=withOutput O (fun q => v (e q)) (pullState e s)) :
    runWithTape (renameRecordedProgram e p) m k s=withOutput (O.image e) v s := by
  apply pullState_equiv_injective e
  rw [runWithTape_rename e e.injective,output,pullState_withOutput_image]

/-- Clean unowned sites transport pointwise through the real interpreter. -/
theorem runWithTape_permutation_clean (e : Equiv.Perm Wire) (p : RecordedProgram)
    (arena owned : Finset Wire) (m : List Bool) (k : Nat) (s : State)
    (clean : ∀q∈arena,q∉owned → (runWithTape p m k (pullState e s)).basis q=false) :
    ∀q∈arena.image e,q∉owned.image e →
      (runWithTape (renameRecordedProgram e p) m k s).basis q=false := by
  intro q hq hn
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
  have no : a∉owned := fun h => hn (Finset.mem_image_of_mem _ h)
  have pull := runWithTape_rename e e.injective p m k s
  exact (congrArg (fun t : State => t.basis a) pull).trans (clean a ha no)

end ECDSAAdd
