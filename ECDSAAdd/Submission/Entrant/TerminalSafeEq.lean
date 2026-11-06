import ECDSAAdd.Submission.Entrant.MainPart07

namespace ECDSAAdd.Entrant.TerminalSafeEq
open ECDSAAdd Arithmetic MeasuredCodec5
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run

theorem of_law (P Q : Program) (v : Nat)
    (law : safe P v=true ∧ safe Q v=true ∧ bitRun P v=bitRun Q v) (m n : List Bool) :
    run P m ⟨false,bitsOf v⟩=run Q n ⟨false,bitsOf v⟩ := by
  rw [run_sim,run_sim,sim_safe _ _ law.1,sim_safe _ _ law.2.1,law.2.2]

end ECDSAAdd.Entrant.TerminalSafeEq
