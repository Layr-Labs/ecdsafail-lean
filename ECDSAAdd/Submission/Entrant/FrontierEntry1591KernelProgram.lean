import ECDSAAdd.Submission.Entrant.FrontierEntry1591PhaseProgram
import ECDSAAdd.Submission.Entrant.FrontierEntry1591Field

namespace ECDSAAdd.Entrant.FrontierEntry1591Kernel
open Arithmetic MappedCompressed DirectSkywalk

def rawEntry : Program :=
  FrontierEntry1591Native.kernel firstPhase FrontierEntry1591Field.entry lastPhase

def rawExit : Program :=
  FrontierEntry1591Native.kernel firstPhase FrontierEntry1591Field.exit lastPhase

def entryKernel : Program :=
  FrontierEntry1591Native.relocated firstPhase FrontierEntry1591Field.entry lastPhase

def exitKernel : Program :=
  FrontierEntry1591Native.relocated firstPhase FrontierEntry1591Field.exit lastPhase

end ECDSAAdd.Entrant.FrontierEntry1591Kernel
