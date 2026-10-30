import ECDSAAdd.Submission.Entrant.FrontierEntry1591Native
import ECDSAAdd.Submission.Entrant.FrontierEntry1591Forward
import ECDSAAdd.Submission.Entrant.FrontierEntry1591Inverse
import ECDSAAdd.Submission.Entrant.FrontierEntry1591KernelCompose

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk Secp256k1
attribute [local irreducible] run wires NewStackOB5.stackForwardT NewStackOB5.stackReverseT

def firstPhase : Program := FrontierEntry1591Native.forward base ++
  (NewStackOB5.stackForwardT ++ skywalkArithmeticClear base)

def lastPhase : Program := skywalkArithmeticClear base ++
  (NewStackOB5.stackReverseT ++ FrontierEntry1591Native.inverse base)

theorem forward_pool : wires NewStackOB5.stackForwardT⊆(skywalkPoolWires base).toFinset := by
  rw [NewStackOB5.stackForwardT_support_eq]
  exact EntryFuse.forward_pool5

theorem first_pool : wires firstPhase⊆(skywalkPoolWires base).toFinset := by
  simp only [firstPhase,wires_append,Finset.union_subset_iff]
  exact ⟨(FrontierEntry1591Native.native_pool base base_pool_nodup).1,
    forward_pool,EntryFuse.clear_pool5⟩

theorem last_pool : wires lastPhase⊆(skywalkPoolWires base).toFinset := by
  simp only [lastPhase,wires_append,Finset.union_subset_iff]
  exact ⟨EntryFuse.clear_pool5,NewStackOB5.stackReverseT_pool,
    (FrontierEntry1591Native.native_pool base base_pool_nodup).2⟩

end ECDSAAdd.Entrant.FrontierEntry1591Kernel
