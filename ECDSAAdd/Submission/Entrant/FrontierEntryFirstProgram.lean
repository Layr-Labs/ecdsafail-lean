import ECDSAAdd.Submission.Entrant.OneFlag
import ECDSAAdd.Submission.Entrant.FrontierEntry1592Support

set_option maxRecDepth 8192
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField MappedCompressed
abbrev ports : BalancedCircuit.Layout := loanPorts1592
theorem ports_q6 : ports=Q6EndpointCell.ports base (base 2409) := rfl
theorem ports_widths : ports.Widths := loanPorts1592_widths
theorem ports_r : ports.r=(balancedSharedPorts base (base 2409)).r := rfl
theorem ports_y : ports.y=(balancedSharedPorts base (base 2409)).y := rfl
def remainingLetters : List MixedTranscriptLetter := (List.range' 2 3).map tapeLetter
def firstBody : Program :=
  joint1592 ++ SW.selW (base 1029) (base 2409) OneFlagSW.swapBody ++
    OneFlagSW.rawReplayS true remainingLetters
def baseFirstPacket : Program := History5.decode base 0 ++ firstBody ++ History5.encode base 0
def firstPacket : Program := renameProgram (shifted (Placement5.pi 0)) baseFirstPacket
end ECDSAAdd.Entrant.FrontierEntry
