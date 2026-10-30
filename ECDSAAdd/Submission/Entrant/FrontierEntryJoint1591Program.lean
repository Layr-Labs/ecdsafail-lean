import ECDSAAdd.Submission.Entrant.FrontierEntry1591KernelProgram
import ECDSAAdd.Submission.Entrant.FrontierEntryFirstProgram

/-! Replace only the forward entry replay's first packet. -/
namespace ECDSAAdd.Entrant.FrontierEntryJoint1591
open Arithmetic MappedCompressed DirectSkywalk

def baseFirstPacket : Program :=
  NewHistory5.decode base 0 ++ FrontierEntry.firstBody ++ NewHistory5.encode base 0

def firstPacket : Program :=
  renameProgram (shifted (Placement5.pi 0)) baseFirstPacket

def logicalReplay : Program :=
  firstPacket ++ FrontierSW1591.groupsS true 1 101 ++ FrontierSW1591.endPacketS true

def replay : Program := renameProgram (OB5.sig 511) logicalReplay

def entryField : Program := replay ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)

def entryHosted : Program := FrontierEntry1591Field.hosted entryField

def entry : Program := ParityField1591.program FrontierEntry1591Field.controls
  FrontierEntry1591Field.work FrontierEntry1591Field.host entryHosted

def rawEntryKernel : Program := FrontierEntry1591Native.kernel
  FrontierEntry1591Kernel.firstPhase entry FrontierEntry1591Kernel.lastPhase

def entryKernel : Program := FrontierEntry1591Native.relocated
  FrontierEntry1591Kernel.firstPhase entry FrontierEntry1591Kernel.lastPhase

end ECDSAAdd.Entrant.FrontierEntryJoint1591
