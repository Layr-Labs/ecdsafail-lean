import ECDSAAdd.Arithmetic.RecordedRailCarryProof
import ECDSAAdd.Arithmetic.Registers

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailRipple
open RecordedRailCarry

/-- Literal pinned9db terminal_step (heo_carry.rs440–461) on two distinct
source bits: no source-top alias, no separately allocated terminal carry. -/
def terminalStep (a0 a1 b0 b1 : Wire) (prev : Option Wire) : Program :=
  match prev with
  | none => [.CCX a0 b0 b1,.CX a1 b1,.CX a0 b0]
  | some p => [.CX p a0,.CX p b0,.CCX a0 b0 b1,.CX p b1,
      .CX a1 b1,.CX p a0,.CX a0 b0]

def topStep (a b : Wire) (prev : Option Wire) : Program :=
  match prev with
  | none => [.CX a b]
  | some p => [.CX p b,.CX a b]

def oldCorrection (carry : Wire) : Option Nat → RecordedProgram
  | none => []
  | some ordinal => [.phaseFromRecord ordinal [.Z carry]]

/-- Normal wrapped rail_ripple: all forward computes precede the terminal;
all old Z corrections and fresh-MX unwinds occur in reverse carry order.
Invalid lengths emit []; the unsigned contract will require aligned lists. -/
def ripple : List Wire → List Wire → Option Wire → List Wire → List (Option Nat) → RecordedProgram
  | [a], [b], prev, [], [] => embedRecorded (topStep a b prev)
  | [a0,a1], [b0,b1], prev, [], [] => embedRecorded (terminalStep a0 a1 b0 b1 prev)
  | a0::a1::a2::as, b0::b1::b2::bs, prev, c::cs, d::ds =>
      embedRecorded (carryStep a0 b0 prev c) ++
      ripple (a1::a2::as) (b1::b2::bs) (some c) cs ds ++
      oldCorrection c d ++ embedRecorded (unwindStep a0 b0 prev c)
  | _, _, _, _, _ => []

theorem terminal_counts (a0 a1 b0 b1 : Wire) (prev : Option Wire) :
    recordedToffoliCount (embedRecorded (terminalStep a0 a1 b0 b1 prev))=1 ∧
    recordedMeasurementCount (embedRecorded (terminalStep a0 a1 b0 b1 prev))=0 := by
  cases prev <;> simp [terminalStep,embedRecorded,recordedToffoliCount,
    recordedMeasurementCount,toffoliCount,measurementCount]

theorem top_counts (a b : Wire) (prev : Option Wire) :
    recordedToffoliCount (embedRecorded (topStep a b prev))=0 ∧
    recordedMeasurementCount (embedRecorded (topStep a b prev))=0 := by
  cases prev <;> simp [topStep,embedRecorded,recordedToffoliCount,
    recordedMeasurementCount,toffoliCount,measurementCount]

theorem oldCorrection_counts (c : Wire) (d : Option Nat) :
    recordedToffoliCount (oldCorrection c d)=0 ∧ recordedMeasurementCount (oldCorrection c d)=0 := by
  cases d <;> simp [oldCorrection,recordedToffoliCount,recordedMeasurementCount]

theorem terminal_support_some (a0 a1 b0 b1 p : Wire) :
    recordedWires (embedRecorded (terminalStep a0 a1 b0 b1 (some p)))={a0,a1,b0,b1,p} := by
  ext q
  simp [terminalStep,embedRecorded,recordedWires,RecordedInstr.quantumWires,Instr.wires]
  all_goals tauto

theorem terminal_support_none (a0 a1 b0 b1 : Wire) :
    recordedWires (embedRecorded (terminalStep a0 a1 b0 b1 none))={a0,a1,b0,b1} := by
  ext q
  simp [terminalStep,embedRecorded,recordedWires,RecordedInstr.quantumWires,Instr.wires]
  all_goals tauto

end ECDSAAdd.Arithmetic.RecordedRailRipple
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.terminal_counts
