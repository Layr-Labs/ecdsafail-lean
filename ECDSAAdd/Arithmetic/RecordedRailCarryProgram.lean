import ECDSAAdd.Framework.RecordedSemantics

set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailCarry

/-- Literal normal (not REVERSE_LOW-reused) carry_step at pinned9db31da9,
heo_carry.rs389–397. Both dressed inputs remain dressed for the unwind. -/
def carryStep (a b : Wire) (prev : Option Wire) (carry : Wire) : Program :=
  match prev with
  | none => [.CCX a b carry]
  | some p => [.CX p a,.CX p b,.CCX a b carry,.CX p carry]

/-- Literal non-SHARED_LOW normal unwind at pinned9db31da9 lines424–435.
The fresh measurement uses its own immediate CZ correction, never the old Z. -/
def unwindStep (a b : Wire) (prev : Option Wire) (carry : Wire) : Program :=
  match prev with
  | none => [.measureX carry [] [.CZ a b],.CX a b]
  | some p => [.CX p carry,.measureX carry [] [.CZ a b],.CX p a,.CX a b]

/-- The source's deferred Z is emitted before unwind while carry still equals
the arithmetic carry. Its ordinal names the old mirror measurement. -/
def retire (a b : Wire) (prev : Option Wire) (carry oldOrdinal : Nat) : RecordedProgram :=
  [.phaseFromRecord oldOrdinal [.Z carry]] ++ embedRecorded (unwindStep a b prev carry)

def program (a b : Wire) (prev : Option Wire) (carry oldOrdinal : Nat) : RecordedProgram :=
  embedRecorded (carryStep a b prev carry) ++ retire a b prev carry oldOrdinal

/-- Arithmetic carry of the normal rail step, including the optional previous
carry. The incoming phase debt can depend on this Boolean before recomputation. -/
def carryValue (a b : Wire) (prev : Option Wire) (bits : BasisState) : Bool :=
  match prev with
  | none => bits a && bits b
  | some p => ((bits a ^^ bits p) && (bits b ^^ bits p)) ^^ bits p

theorem carry_measurements (a b : Wire) (prev : Option Wire) (carry : Wire) :
    recordedMeasurementCount (embedRecorded (carryStep a b prev carry))=0 := by
  cases prev <;> simp [carryStep,embedRecorded,recordedMeasurementCount,measurementCount]

theorem counts (a b : Wire) (prev : Option Wire) (carry oldOrdinal : Nat) :
    recordedToffoliCount (program a b prev carry oldOrdinal)=1 ∧
    recordedMeasurementCount (program a b prev carry oldOrdinal)=1 ∧
    recordedToffoliCount (retire a b prev carry oldOrdinal)=0 ∧
    recordedMeasurementCount (retire a b prev carry oldOrdinal)=1 := by
  cases prev <;> simp [program,retire,carryStep,unwindStep,embedRecorded,
    recordedToffoliCount,recordedMeasurementCount,toffoliCount,measurementCount]

theorem support_some (a b p carry oldOrdinal : Nat) :
    recordedWires (program a b (some p) carry oldOrdinal)={a,b,p,carry} ∧
    recordedSources (program a b (some p) carry oldOrdinal)={oldOrdinal} := by
  constructor
  · ext q
    simp [program,retire,carryStep,unwindStep,embedRecorded,recordedWires,
      RecordedInstr.quantumWires,Instr.wires,correctionWires]
    all_goals tauto
  · simp [program,retire,carryStep,unwindStep,embedRecorded,recordedSources]

theorem support_none (a b carry oldOrdinal : Nat) :
    recordedWires (program a b none carry oldOrdinal)={a,b,carry} ∧
    recordedSources (program a b none carry oldOrdinal)={oldOrdinal} := by
  constructor
  · ext q
    simp [program,retire,carryStep,unwindStep,embedRecorded,recordedWires,
      RecordedInstr.quantumWires,Instr.wires,correctionWires]
    all_goals tauto
  · simp [program,retire,carryStep,unwindStep,embedRecorded,recordedSources]

theorem wellFormed (a b : Wire) (prev : Option Wire) (carry oldOrdinal cursor : Nat)
    (earlier : oldOrdinal < cursor) :
    RecordedWellFormedAt cursor (program a b prev carry oldOrdinal) := by
  cases prev <;> simp [program,retire,carryStep,unwindStep,embedRecorded,
    RecordedWellFormedAt,measurementCount,earlier]

end ECDSAAdd.Arithmetic.RecordedRailCarry
#print axioms ECDSAAdd.Arithmetic.RecordedRailCarry.counts
#print axioms ECDSAAdd.Arithmetic.RecordedRailCarry.support_some
