import ECDSAAdd.Framework.RecordedSemantics

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
namespace ECDSAAdd

/-- Relocate classical ordinals when placing a closed recorded segment after
earlier measurements. Quantum wire identities are deliberately unchanged. -/
def relocateRecord (offset : Nat) : RecordedInstr → RecordedInstr
  | .gate i => .gate i
  | .phaseFromRecord j cs => .phaseFromRecord (offset+j) cs

def relocateRecords (offset : Nat) (p : RecordedProgram) : RecordedProgram :=
  p.map (relocateRecord offset)

theorem relocateRecords_counts (offset : Nat) (p : RecordedProgram) :
    recordedToffoliCount (relocateRecords offset p)=recordedToffoliCount p ∧
    recordedMeasurementCount (relocateRecords offset p)=recordedMeasurementCount p := by
  induction p with
  | nil => simp [relocateRecords,recordedToffoliCount,recordedMeasurementCount]
  | cons i p ih =>
    cases i <;> simp [relocateRecords,relocateRecord,recordedToffoliCount,
      recordedMeasurementCount] at ih ⊢ <;> omega

theorem relocateRecords_wires (offset : Nat) (p : RecordedProgram) :
    recordedWires (relocateRecords offset p)=recordedWires p := by
  induction p with
  | nil => simp [relocateRecords,recordedWires]
  | cons i p ih =>
    simp only [relocateRecords] at ih
    cases i <;> simp [relocateRecords,relocateRecord,recordedWires,
      RecordedInstr.quantumWires,ih]

theorem relocateRecords_wellFormed (offset k : Nat) (p : RecordedProgram) :
    RecordedWellFormedAt (offset+k) (relocateRecords offset p) ↔
      RecordedWellFormedAt k p := by
  induction p generalizing k with
  | nil => simp [relocateRecords,RecordedWellFormedAt]
  | cons i p ih =>
    simp only [relocateRecords] at ih
    cases i with
    | gate i =>
      simpa only [relocateRecords,List.map_cons,relocateRecord,RecordedWellFormedAt,
        Nat.add_assoc] using ih (k+measurementCount [i])
    | phaseFromRecord j cs =>
      simp only [relocateRecords,List.map_cons,relocateRecord,RecordedWellFormedAt]
      rw [Nat.add_lt_add_iff_left,ih]

private theorem getD_drop (m : List Bool) (offset j : Nat) :
    (m.drop offset).getD j false=m.getD (offset+j) false := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_drop]

/-- Placement preserves every basis bit, arbitrary incoming phase and every
measurement tape. A mirror still reads the original outcome after relocation. -/
theorem runWithTape_relocate (p : RecordedProgram) (offset k : Nat)
    (m : List Bool) (s : State) :
    runWithTape (relocateRecords offset p) m (offset+k) s=
      runWithTape p (m.drop offset) k s := by
  induction p generalizing k s with
  | nil => rfl
  | cons i p ih =>
    simp only [relocateRecords] at ih
    cases i with
    | gate i =>
      simp only [relocateRecords,List.map_cons,relocateRecord,runWithTape]
      rw [Nat.add_assoc,ih,List.drop_drop]
    | phaseFromRecord j cs =>
      simp only [relocateRecords,List.map_cons,relocateRecord,runWithTape,getD_drop]
      exact ih k _

/-- Closed concatenation owns all its record references. Its second segment
is moved by exactly the first segment's consumed measurement count. -/
def recordedThen (p q : RecordedProgram) : RecordedProgram :=
  p++relocateRecords (recordedMeasurementCount p) q

theorem recordedThen_run (p q : RecordedProgram) (m : List Bool) (s : State) :
    runWithTape (recordedThen p q) m 0 s=
      runWithTape q (m.drop (recordedMeasurementCount p)) 0 (runWithTape p m 0 s) := by
  simp only [recordedThen,runWithTape_append,Nat.zero_add]
  exact runWithTape_relocate q (recordedMeasurementCount p) 0 m _

theorem recordedThen_wellFormed (p q : RecordedProgram)
    (hp : RecordedWellFormedAt 0 p) (hq : RecordedWellFormedAt 0 q) :
    RecordedWellFormedAt 0 (recordedThen p q) := by
  rw [recordedThen,RecordedWellFormedAt_append]
  refine ⟨hp,?_⟩
  simpa only [Nat.zero_add,Nat.add_zero] using
    (relocateRecords_wellFormed (recordedMeasurementCount p) 0 q).mpr hq

end ECDSAAdd
#print axioms ECDSAAdd.runWithTape_relocate
#print axioms ECDSAAdd.recordedThen_run
#print axioms ECDSAAdd.recordedThen_wellFormed
