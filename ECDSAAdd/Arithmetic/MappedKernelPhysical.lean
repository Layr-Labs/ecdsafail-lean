import ECDSAAdd.Arithmetic.MappedFieldPhysical
import ECDSAAdd.Arithmetic.NativeKnownPhysical
import ECDSAAdd.Arithmetic.DirectZeroPhysical
import ECDSAAdd.Arithmetic.MappedCompressedStageSupport
namespace ECDSAAdd.Arithmetic
open RecordedQuantum MappedCompressed

theorem mappedClear_physical : GatePhysical (skywalkArithmeticClear base) := by
  simp [skywalkArithmeticClear,skywalkTerminalClear,base,GatePhysical,PhysicalInstr,ProperGate]

theorem mappedKernel_physical (divide : Bool) : GatePhysical (kernel divide) := by
  have first := (NativeFirstDirect.programs_physical base base_pool_nodup).1
  have loops := compressedLoops_physical base 1 511 (by decide) base_pool_nodup
  have last := NativeFirstKnown.inverse_physical base base_pool_nodup
  have field : GatePhysical (MappedCompressed.selectedFieldSegment divide) := selectedFieldSegment_physical divide
  simp only [kernel,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨first,loops.1⟩,mappedClear_physical⟩,field⟩,mappedClear_physical⟩,loops.2⟩,last⟩

theorem mappedControlled_physical (divide : Bool) : GatePhysical (controlled divide) := by
  apply directZero_physical _ _ _ _ _ _ (mappedKernel_physical divide)
  decide +kernel
end ECDSAAdd.Arithmetic
