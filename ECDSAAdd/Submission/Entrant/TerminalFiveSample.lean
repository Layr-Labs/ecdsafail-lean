import ECDSAAdd.Submission.Entrant.TerminalFiveSupport
import ECDSAAdd.Submission.Entrant.LocalWindowReplace

namespace ECDSAAdd.Entrant.TerminalFiveSample
open ECDSAAdd Arithmetic MappedCompressed Challenge CompactCertificates
open TerminalFiveBridge
set_option maxRecDepth 30000
set_option maxHeartbeats 400000
set_option diagnostics true
attribute [local irreducible] run wires

theorem stage_replace (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (a state : State) (stage : Rolling1588.Integer.Stage base isA x ECDSAAdd.p 506 a.basis)
    (m n : List Bool)
    (agree : ∀q∈TerminalFiveDomain.sites,state.basis q=(run forward [] a).basis q) :
    run physical m state=run TerminalFivePlacement.old n state := by
  obtain ⟨g,s,uv,member,reads⟩ := TerminalFiveDomain.stage506 isA x hx0 hx a stage
  exact LocalWindowReplace.after_forward physical TerminalFivePlacement.old forward TerminalFiveDomain.sites
    physical_support old_support forward_support a state (TerminalFiveDomain.pre g s uv.1 uv.2)
    reads agree m n (sample_run g s uv member m n)

end ECDSAAdd.Entrant.TerminalFiveSample
