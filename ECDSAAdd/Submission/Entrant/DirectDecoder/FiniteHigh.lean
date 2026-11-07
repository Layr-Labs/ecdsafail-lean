import ECDSAAdd.Submission.Entrant.DirectDecoder.FiniteBase
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph

theorem high_local_checked : ∀x : Fin 2048,highValid x.val=true → ∀i : Fin 4,
 evalPoly (highPolys.getD i.val []) (highVars x.val)=(highRs x.val).getD (i.val+2) false := by decide +kernel

end ECDSAAdd.Entrant.DirectDecoder
