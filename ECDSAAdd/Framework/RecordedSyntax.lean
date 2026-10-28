import ECDSAAdd.Framework.Cost

namespace ECDSAAdd

/-- Deferred corrections refer to a previously consumed measurement ordinal.
They read the classical tape and act only on their declared quantum wires. -/
inductive RecordedInstr where
  | gate (instruction : Instr)
  | phaseFromRecord (measurementOrdinal : Nat) (corrections : List Correction)
  deriving DecidableEq, Repr

abbrev RecordedProgram := List RecordedInstr

def embedRecorded (p : Program) : RecordedProgram := p.map RecordedInstr.gate

def recordedMeasurementCount : RecordedProgram → Nat
  | [] => 0
  | .gate i :: p => measurementCount [i] + recordedMeasurementCount p
  | .phaseFromRecord _ _ :: p => recordedMeasurementCount p

def recordedToffoliCount : RecordedProgram → Nat
  | [] => 0
  | .gate i :: p => toffoliCount [i] + recordedToffoliCount p
  | .phaseFromRecord _ _ :: p => recordedToffoliCount p

def RecordedInstr.quantumWires : RecordedInstr → Finset Wire
  | .gate i => i.wires
  | .phaseFromRecord _ cs => correctionWires cs

def recordedWires : RecordedProgram → Finset Wire
  | [] => ∅
  | i :: p => i.quantumWires ∪ recordedWires p

/-- Classical record identifiers are accounted separately from quantum support. -/
def recordedSources : RecordedProgram → Finset Nat
  | [] => ∅
  | .gate _ :: p => recordedSources p
  | .phaseFromRecord j _ :: p => {j} ∪ recordedSources p

/-- The tape is fixed across composition; cursor counts consumed measurements. -/
structure RecordedContext where
  tape : List Bool
  cursor : Nat

/-- A deferred correction may refer only to an earlier measurement, even when
an arbitrary finite tape is shorter than the consumed prefix (then it reads 0). -/
def RecordedWellFormedAt : Nat → RecordedProgram → Prop
  | _, [] => True
  | k, .gate i :: p => RecordedWellFormedAt (k + measurementCount [i]) p
  | k, .phaseFromRecord j _ :: p => j < k ∧ RecordedWellFormedAt k p

@[simp] theorem recordedMeasurementCount_append (p q : RecordedProgram) :
    recordedMeasurementCount (p ++ q)=recordedMeasurementCount p+recordedMeasurementCount q := by
  induction p with
  | nil => simp [recordedMeasurementCount]
  | cons i p ih => cases i <;> simp [recordedMeasurementCount,ih,Nat.add_assoc]

@[simp] theorem recordedToffoliCount_append (p q : RecordedProgram) :
    recordedToffoliCount (p ++ q)=recordedToffoliCount p+recordedToffoliCount q := by
  induction p with
  | nil => simp [recordedToffoliCount]
  | cons i p ih => cases i <;> simp [recordedToffoliCount,ih,Nat.add_assoc]

@[simp] theorem recordedWires_append (p q : RecordedProgram) :
    recordedWires (p ++ q)=recordedWires p ∪ recordedWires q := by
  induction p with
  | nil => simp [recordedWires]
  | cons i p ih => simp [recordedWires,ih,Finset.union_assoc]

@[simp] theorem embedRecorded_counts (p : Program) :
    recordedToffoliCount (embedRecorded p)=toffoliCount p ∧
    recordedMeasurementCount (embedRecorded p)=measurementCount p := by
  induction p with
  | nil => simp [embedRecorded,recordedToffoliCount,recordedMeasurementCount,toffoliCount,measurementCount]
  | cons i p ih =>
    simp only [embedRecorded] at ih
    cases i <;> simp [embedRecorded,recordedToffoliCount,recordedMeasurementCount,
      toffoliCount,measurementCount,ih]

@[simp] theorem embedRecorded_wires (p : Program) : recordedWires (embedRecorded p)=wires p := by
  induction p with
  | nil => simp [embedRecorded,recordedWires,wires]
  | cons i p ih =>
    simp only [embedRecorded] at ih
    simp [embedRecorded,recordedWires,RecordedInstr.quantumWires,wires,ih]

@[simp] theorem phaseFromRecord_resources (j : Nat) (cs : List Correction) :
    recordedToffoliCount [.phaseFromRecord j cs]=0 ∧
    recordedMeasurementCount [.phaseFromRecord j cs]=0 ∧
    recordedWires [.phaseFromRecord j cs]=correctionWires cs ∧
    recordedSources [.phaseFromRecord j cs]={j} := by
  simp [recordedToffoliCount,recordedMeasurementCount,recordedWires,
    RecordedInstr.quantumWires,recordedSources]

theorem RecordedWellFormedAt_append (k : Nat) (p q : RecordedProgram) :
    RecordedWellFormedAt k (p++q) ↔ RecordedWellFormedAt k p ∧
      RecordedWellFormedAt (k+recordedMeasurementCount p) q := by
  induction p generalizing k with
  | nil => simp [RecordedWellFormedAt,recordedMeasurementCount]
  | cons i p ih => cases i <;> simp [RecordedWellFormedAt,recordedMeasurementCount,ih,Nat.add_assoc,and_assoc]

/-- The finite classical source inventory never reaches beyond the final cursor.
No classical history is hidden in the quantum support certificate. -/
theorem recordedSources_bound (p : RecordedProgram) (k : Nat)
    (h : RecordedWellFormedAt k p) :
    ∀ j ∈ recordedSources p, j < k+recordedMeasurementCount p := by
  induction p generalizing k with
  | nil => simp [recordedSources]
  | cons i p ih =>
    cases i with
    | gate i =>
      simpa only [recordedSources,recordedMeasurementCount,Nat.add_assoc] using ih _ h
    | phaseFromRecord j cs =>
      intro q hq
      simp only [recordedSources,Finset.mem_union,Finset.mem_singleton] at hq
      rcases hq with rfl|hq
      · exact lt_of_lt_of_le h.1 (Nat.le_add_right _ _)
      · exact ih k h.2 q hq

/-- All source identifiers form an explicit finite prefix subset. This counts
classical references separately, without treating them as free quantum cache. -/
theorem recordedSources_card_le (p : RecordedProgram) (k : Nat)
    (h : RecordedWellFormedAt k p) :
    (recordedSources p).card ≤ k+recordedMeasurementCount p := by
  have subset : recordedSources p ⊆ Finset.range (k+recordedMeasurementCount p) := by
    intro j hj
    exact Finset.mem_range.mpr (recordedSources_bound p k h j hj)
  simpa only [Finset.card_range] using Finset.card_le_card subset

@[simp] theorem embedRecorded_sources (p : Program) : recordedSources (embedRecorded p)=∅ := by
  induction p with
  | nil => rfl
  | cons i p ih => simpa only [embedRecorded,List.map_cons,recordedSources] using ih

@[simp] theorem embedRecorded_wellFormed (p : Program) (k : Nat) :
    RecordedWellFormedAt k (embedRecorded p) := by
  induction p generalizing k with
  | nil => trivial
  | cons i p ih => exact ih (k+measurementCount [i])

end ECDSAAdd
#print axioms ECDSAAdd.embedRecorded_counts
#print axioms ECDSAAdd.recordedSources_bound
