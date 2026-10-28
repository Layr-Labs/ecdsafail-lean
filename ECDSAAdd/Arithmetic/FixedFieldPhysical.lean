import ECDSAAdd.Arithmetic.PhysicalGateCheck
import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalCell
import ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonicalCell
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
namespace ECDSAAdd.Arithmetic
open RecordedQuantum
theorem fixedForwardField_physical : GatePhysical (OffsetBorrowedField.program id 2409) := by
  apply physicalGateCheck_correct
  decide +kernel

theorem fixedInverseField_physical : GatePhysical (OffsetBorrowedInverse.program id 2409) := by
  apply physicalGateCheck_correct
  decide +kernel
end ECDSAAdd.Arithmetic
