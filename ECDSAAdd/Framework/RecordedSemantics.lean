import ECDSAAdd.Framework.RecordedSyntax

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd

/-- Absolute ordinals always index the same tape. A deferred correction
consumes no outcome and never replaces the old measurement by an inverse one. -/
def runWithTape : RecordedProgram → List Bool → Nat → State → State
  | [], _, _, s => s
  | .gate i :: p, m, k, s =>
      runWithTape p m (k+measurementCount [i]) (run [i] (m.drop k) s)
  | .phaseFromRecord j cs :: p, m, k, s =>
      runWithTape p m k (if m.getD j false then correct cs s else s)

def runRecorded (p : RecordedProgram) (ctx : RecordedContext) (s : State) : State × RecordedContext :=
  (runWithTape p ctx.tape ctx.cursor s,
    ⟨ctx.tape,ctx.cursor+recordedMeasurementCount p⟩)

private theorem tape_drop_succ (m : List Bool) (k : Nat) :
    m.drop (k+1)=(m.drop k).tail := by
  have tail : (m.drop k).tail=(m.drop k).drop 1 := by
    cases m.drop k <;> rfl
  rw [tail,List.drop_drop]

/-- Embedding preserves all basis bits and arbitrary input phase on every tape,
including short and empty tapes. The original interpreter is unchanged. -/
theorem runWithTape_embedRecorded (p : Program) (m : List Bool) (k : Nat) (s : State) :
    runWithTape (embedRecorded p) m k s=run p (m.drop k) s := by
  induction p generalizing k s with
  | nil => rfl
  | cons i p ih =>
    simp only [embedRecorded,List.map_cons,runWithTape]
    rw [show List.map RecordedInstr.gate p=embedRecorded p from rfl,ih]
    cases i <;> simp only [measurementCount,Nat.add_zero,run]
    rw [tape_drop_succ]

/-- Recorded segment composition must retain the global tape. Only its cursor
advances; absolute deferred record references are never rebased or dropped. -/
theorem runWithTape_append (p q : RecordedProgram) (m : List Bool) (k : Nat) (s : State) :
    runWithTape (p++q) m k s=
      runWithTape q m (k+recordedMeasurementCount p) (runWithTape p m k s) := by
  induction p generalizing k s with
  | nil => simp [runWithTape,recordedMeasurementCount]
  | cons i p ih =>
    cases i <;> simp only [List.cons_append,runWithTape,recordedMeasurementCount]
    · rw [ih]
      simp only [Nat.add_assoc]
    · exact ih k _

theorem runRecorded_append (p q : RecordedProgram) (ctx : RecordedContext) (s : State) :
    runRecorded (p++q) ctx s=
      runRecorded q (runRecorded p ctx s).2 (runRecorded p ctx s).1 := by
  simp only [runRecorded,recordedMeasurementCount_append,runWithTape_append,Nat.add_assoc]

@[simp] theorem runRecorded_tape (p : RecordedProgram) (ctx : RecordedContext) (s : State) :
    (runRecorded p ctx s).2.tape=ctx.tape := rfl

@[simp] theorem runRecorded_cursor (p : RecordedProgram) (ctx : RecordedContext) (s : State) :
    (runRecorded p ctx s).2.cursor=ctx.cursor+recordedMeasurementCount p := rfl

@[simp] theorem runWithTape_phaseFromRecord (j : Nat) (cs : List Correction)
    (m : List Bool) (k : Nat) (s : State) :
    runWithTape [.phaseFromRecord j cs] m k s=
      if m.getD j false then correct cs s else s := rfl

/-- Deferred phase work has no basis mutation, even for a malformed ordinal.
Well-formedness separately guarantees that the ordinal names an earlier MX. -/
theorem runWithTape_phaseFromRecord_basis (j : Nat) (cs : List Correction)
    (m : List Bool) (k : Nat) (s : State) :
    (runWithTape [.phaseFromRecord j cs] m k s).basis=s.basis := by
  rw [runWithTape_phaseFromRecord]
  split <;> simp

/-- Actual emitted quantum support includes every immediate and deferred
correction operand, while classical ordinals occupy no quantum wire. -/
theorem runWithTape_preserves_outside (p : RecordedProgram) (m : List Bool) (k : Nat)
    (s : State) (q : Wire) (hq : q∉recordedWires p) :
    (runWithTape p m k s).basis q=s.basis q := by
  induction p generalizing k s with
  | nil => rfl
  | cons i p ih =>
    have hi : q∉i.quantumWires := fun h => hq (Finset.mem_union_left _ h)
    have hp : q∉recordedWires p := fun h => hq (Finset.mem_union_right _ h)
    cases i with
    | gate i =>
      rw [runWithTape,ih _ _ hp]
      exact run_preserves_outside [i] (m.drop k) s q
        (by simpa only [wires,Finset.union_empty,RecordedInstr.quantumWires] using hi)
    | phaseFromRecord j cs =>
      rw [runWithTape,ih _ _ hp]
      split <;> simp

/-- One bare measurement followed by deferred Z correction refers to that
measurement's absolute ordinal; the tape cursor still advances exactly once. -/
def deferredErase (target : Wire) (oldOrdinal : Nat) (recomputed : Wire) : RecordedProgram :=
  [.gate (.measureX target [] []),.phaseFromRecord oldOrdinal [.Z recomputed]]

theorem deferredErase_counts (target : Wire) (j : Nat) (r : Wire) :
    recordedToffoliCount (deferredErase target j r)=0 ∧
    recordedMeasurementCount (deferredErase target j r)=1 ∧
    recordedWires (deferredErase target j r)={target,r} := by
  simp [deferredErase,recordedToffoliCount,recordedMeasurementCount,
    toffoliCount,measurementCount,recordedWires,RecordedInstr.quantumWires,
    Instr.wires,correctionWires,Finset.insert_comm]

end ECDSAAdd
#print axioms ECDSAAdd.runWithTape_embedRecorded
#print axioms ECDSAAdd.runWithTape_append
#print axioms ECDSAAdd.runWithTape_preserves_outside
