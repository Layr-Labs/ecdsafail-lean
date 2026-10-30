import ECDSAAdd.Submission.Entrant.FrontierEntryReplayProgram
import ECDSAAdd.Submission.Entrant.FrontierCurrent

/-! The joint entry changes only the forward replay's first packet. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntryKernel
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk BalancedField History5

def field5S : Program :=
  FrontierEntry.replay ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)

def hostField5S : Program :=
  [.X (base 511)] ++ (renameProgram HostOB5.hostSwap field5S ++ [.X (base 511)])

def baseKernel : Program := Q5FusionPhase.relocated hostField5S

def kernel5S : Program := Q7FusionPhase.relocated hostField5S

end ECDSAAdd.Entrant.FrontierEntryKernel
