import ECDSAAdd.Submission.Entrant.MainPre
import ECDSAAdd.Submission.Entrant.FrontierEntry1593Support

/-! Forward first-body replacement for the fixed rapid frontier. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField MappedCompressed

abbrev ports : BalancedCircuit.Layout := OneBankCell5.ports base (base 2409)


def remainingLetters : List MixedTranscriptLetter :=
  (List.range' 2 3).map tapeLetter

def firstBody : Program :=
  joint1593 ++
    SW.selW (base 1029) (base 2410) SW.swapBody ++
      SW.rawReplayS true remainingLetters

def baseFirstPacket : Program :=
  History5.decode base 0 ++ firstBody ++ History5.encode base 0

def firstPacket : Program :=
  renameProgram (shifted (Placement5.pi 0)) baseFirstPacket


end ECDSAAdd.Entrant.FrontierEntry
