import ECDSAAdd.Submission.Entrant.FrontierEntryFirstProgram

/-! Program definitions shared by the semantic and resource proofs. -/
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic Secp256k1 MappedCompressed

def logicalReplay : Program :=
  firstPacket ++ OneFlagSW.groupsS true 1 101 ++ OneFlagSW.endPacketS true

def replay : Program := renameProgram (OB5.sig 511) logicalReplay

/-- The old packet uses its own record tape; the unchanged suffix keeps the new tape. -/
def oldRecords (m : List Bool) : List Bool :=
  List.replicate (measurementCount (OneFlagSW.firstPacketS true)) false ++
    m.drop (measurementCount firstPacket)


end ECDSAAdd.Entrant.FrontierEntry
