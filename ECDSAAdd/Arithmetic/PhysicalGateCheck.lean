import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
namespace ECDSAAdd.Arithmetic
open RecordedQuantum
def physicalGateCheck : Instr → Bool
  | .X _ => true
  | .CX a t => a != t
  | .CCX a b t => (a != t) && (b != t)
  | .measureX _ _ _ => true

theorem physicalGateCheck_correct (p : Program) (h : p.all physicalGateCheck = true) :
    GatePhysical p := by
  intro i hi
  have hh := List.all_eq_true.mp h i hi
  cases i with
  | X t => trivial
  | measureX t c d => trivial
  | CX a t => simpa [physicalGateCheck,PhysicalInstr,ProperGate] using hh
  | CCX a b t => simpa [physicalGateCheck,PhysicalInstr,ProperGate] using hh

end ECDSAAdd.Arithmetic
