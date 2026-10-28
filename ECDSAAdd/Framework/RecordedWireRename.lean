import ECDSAAdd.Framework.RecordedRelocation
import ECDSAAdd.Framework.WireRename

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
namespace ECDSAAdd

/-- Quantum placement changes every correction operand, but never changes a
classical measurement identifier. Record relocation is a separate operation. -/
def renameRecordedInstr (f : Wire → Wire) : RecordedInstr → RecordedInstr
  | .gate i => .gate (renameInstr f i)
  | .phaseFromRecord j cs => .phaseFromRecord j (cs.map (renameCorrection f))

def renameRecordedProgram (f : Wire → Wire) (p : RecordedProgram) : RecordedProgram :=
  p.map (renameRecordedInstr f)

theorem renameRecorded_counts (f : Wire → Wire) (p : RecordedProgram) :
    recordedToffoliCount (renameRecordedProgram f p)=recordedToffoliCount p ∧
    recordedMeasurementCount (renameRecordedProgram f p)=recordedMeasurementCount p := by
  induction p with
  | nil => simp [renameRecordedProgram,recordedToffoliCount,recordedMeasurementCount]
  | cons i p ih =>
    simp only [renameRecordedProgram] at ih
    cases i with
    | gate i =>
      have counts := renameProgram_counts f [i]
      simp only [renameProgram,List.map_cons,List.map_nil] at counts
      simp only [renameRecordedProgram,List.map_cons,renameRecordedInstr,
        recordedToffoliCount,recordedMeasurementCount,counts.1,counts.2]
      exact ⟨congrArg _ ih.1,congrArg _ ih.2⟩
    | phaseFromRecord j cs =>
      simpa only [renameRecordedProgram,List.map_cons,renameRecordedInstr,
        recordedToffoliCount,recordedMeasurementCount] using ih

theorem renameRecorded_wires (f : Wire → Wire) (p : RecordedProgram) :
    recordedWires (renameRecordedProgram f p)=(recordedWires p).image f := by
  induction p with
  | nil => simp [renameRecordedProgram,recordedWires]
  | cons i p ih =>
    simp only [renameRecordedProgram] at ih
    cases i <;> simp [renameRecordedProgram,renameRecordedInstr,recordedWires,
      RecordedInstr.quantumWires,renameInstr_support,renameCorrection_support,
      Finset.image_union,ih]

theorem renameRecorded_sources (f : Wire → Wire) (p : RecordedProgram) :
    recordedSources (renameRecordedProgram f p)=recordedSources p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [renameRecordedProgram] at ih
    cases i <;> simp [renameRecordedProgram,renameRecordedInstr,recordedSources,ih]

theorem runWithTape_rename (f : Wire → Wire) (hf : Function.Injective f)
    (p : RecordedProgram) (m : List Bool) (k : Nat) (s : State) :
    pullState f (runWithTape (renameRecordedProgram f p) m k s)=
      runWithTape p m k (pullState f s) := by
  induction p generalizing k s with
  | nil => rfl
  | cons i p ih =>
    simp only [renameRecordedProgram] at ih
    cases i with
    | gate i =>
      have counts := renameProgram_counts f [i]
      have step := run_rename f hf [i] (m.drop k) s
      simp only [renameProgram,List.map_cons,List.map_nil] at counts step
      simp only [renameRecordedProgram,List.map_cons,renameRecordedInstr,runWithTape]
      rw [counts.2,ih,step]
    | phaseFromRecord j cs =>
      simp only [renameRecordedProgram,List.map_cons,renameRecordedInstr,runWithTape]
      rw [ih]
      split <;> simp only [pullState_correct]

/-- Relabeling a closed segment and shifting its record base commute. -/
theorem renameRecorded_relocate (f : Wire → Wire) (offset : Nat) (p : RecordedProgram) :
    renameRecordedProgram f (relocateRecords offset p)=
      relocateRecords offset (renameRecordedProgram f p) := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp [renameRecordedProgram,relocateRecords,renameRecordedInstr,
      relocateRecord] at ih ⊢ <;> exact ih

end ECDSAAdd
#print axioms ECDSAAdd.runWithTape_rename
#print axioms ECDSAAdd.renameRecorded_wires
#print axioms ECDSAAdd.renameRecorded_relocate
