import ECDSAAdd.Submission.Entrant.EKSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed

def cands : List Nat :=
  [514, 684, 769, 1027, 1201, 1284, 1400, 1540, 1796, 1797, 2054, 2055,
   2312, 2313, 2400, 2409, 2410, 2411]

def probe (d : Bool) : List (Nat × Bool) :=
  let P := controlled d
  cands.map (fun i => (i, P.any (fun ins => decide (base i ∈ ins.wires))))

#eval (controlled false).length
#eval probe false
#eval probe true

end ECDSAAdd.Entrant
