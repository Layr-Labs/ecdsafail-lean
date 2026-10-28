import Lean

/-! Run ONLY from the evaluator's protected installation with trusted dependencies.
The optional path argument is an evaluator-created overlay containing trusted dependencies and
only the Entrant compiled artifacts from the worker. No entrant is imported while this file elaborates.
Runtime imports do not load extensions or execute initializers. -/
open Lean

private def checked (result : Except Kernel.Exception α) : IO α :=
  match result with
  | .ok a => pure a
  | .error _ => throw <| IO.userError "REJECT: kernel check or reduction failed"

private def checkType (env : Environment) (value expected : Expr) : IO Unit := do
  let actual ← checked (Kernel.check env {} value)
  let _ ← checked (Kernel.check env {} expected)
  unless ← checked (Kernel.isDefEq env {} actual expected) do
    throw <| IO.userError "REJECT: certificate or entry has wrong kernel type"

private def checkAxioms (env : Environment) (name : Name) : IO Unit := do
  let (_, state) := ((CollectAxioms.collect name).run env).run {}
  for ax in state.axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throw <| IO.userError s!"REJECT: non-allowlisted axiom {ax}"

private partial def natValue (env : Environment) (value : Expr) : IO Nat := do
  match ← checked (Kernel.whnf env {} value) with
  | .lit (.natVal n) => pure n
  | .const ``Nat.zero _ => pure 0
  | .app (.const ``Nat.succ _) n => return (← natValue env n) + 1
  | _ => throw <| IO.userError "REJECT: metric did not kernel-reduce to a natural number"

private def field (name : Name) (arg : Expr) : Expr := mkApp (mkConst name) arg

unsafe def main (args : List String) : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    match args with
    | [] => pure ()
    | [overlay] => searchPathRef.modify (System.FilePath.mk overlay :: ·)
    | _ => throw <| IO.userError "usage: trusted judge.lean [sealed entrant artifact overlay]"
    let env ← importModules #[{ module := `ECDSAAdd.Judge.Main },
      { module := `ECDSAAdd.Submission.Entrant.Main }] {} (loadExts := false)
    let entry := mkConst `ECDSAAdd.Entrant.entry
    let bounds := mkConst `ECDSAAdd.Entrant.bounds
    checkType env entry (mkConst `ECDSAAdd.Challenge.Entry)
    checkType env bounds (mkConst `ECDSAAdd.Challenge.Bounds)
    let target := mkAppN (mkConst `ECDSAAdd.Judge.acceptance) #[entry, bounds]
    checkType env (mkConst `ECDSAAdd.Entrant.certificate) target
    for name in [`ECDSAAdd.Entrant.entry, `ECDSAAdd.Entrant.bounds,
        `ECDSAAdd.Entrant.certificate] do
      checkAxioms env name
    let t ← natValue env (field `ECDSAAdd.Challenge.Bounds.toffoli bounds)
    let q ← natValue env (field `ECDSAAdd.Challenge.Bounds.qubits bounds)
    let m ← natValue env (field `ECDSAAdd.Challenge.Bounds.measurements bounds)
    let slots ← natValue env (field `ECDSAAdd.Challenge.Bounds.gateSlots bounds)
    IO.println (Json.mkObj [
      ("accepted", toJson true), ("score_toffoli_upper_bound", toJson t),
      ("qubits_upper_bound", toJson q), ("measurements_upper_bound", toJson m),
      ("all_syntax_slots_upper_bound", toJson slots),
      ("qubits_times_toffoli_upper_bound", toJson (q*t))]).compress
    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"judge rejected: {e}"
    return (1 : UInt32)
