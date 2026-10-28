import ECDSAAdd.Challenge.Regression
import ECDSAAdd.Judge.Main
open Lean
private def audited : List Name := [
  ``ECDSAAdd.Challenge.Certificate.phase_restored,
  ``ECDSAAdd.Challenge.Certificate.all_work_clean,
  ``ECDSAAdd.Challenge.qubits_ge_io, ``ECDSAAdd.Challenge.qubits_empty,
  ``ECDSAAdd.Challenge.gateSlots_append,
  ``ECDSAAdd.Challenge.Regression.dirty_wire_rejected,
  ``ECDSAAdd.Challenge.Regression.phase_debt_rejected,
  ``ECDSAAdd.Challenge.Regression.aliased_cx_rejected,
  ``ECDSAAdd.Challenge.Regression.aliased_ccx_rejected,
  ``ECDSAAdd.Challenge.Regression.both_correction_branches_counted,
  ``ECDSAAdd.Judge.acceptance]
run_cmd do
  let env ← getEnv
  for name in audited do
    let (_, state) := ((CollectAxioms.collect name).run env).run {}
    for ax in state.axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "non-allowlisted axiom {ax} in {name}"
  logInfo m!"challenge exact axiom audit: {audited.length} entries passed"
