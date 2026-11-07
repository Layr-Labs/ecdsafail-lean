import ECDSAAdd.Submission.Entrant.DirectDecoder.FiniteBase
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DirectDecoder
open Arithmetic TerminalGraph

theorem initial_local_checked : ∀x : Fin 512,(x.val.testBit 6 && x.val.testBit 7)=false → ∀i : Fin 6,
 evalPoly (lowPolys.getD i.val []) (initialVars x.val)=(initialRs x.val).getD i.val false := by decide +kernel

end ECDSAAdd.Entrant.DirectDecoder
