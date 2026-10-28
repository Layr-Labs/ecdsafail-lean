import Lean
import ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer
open Lean Elab Command
private partial def waitingDependencies (env : Environment) (targets : List Name) (directAdmissions : Bool)
    (todo : List Name) (seen : NameSet := {}) (found : List Name := []) : List Name :=
  match todo with
  | [] => found.reverse
  | n :: rest =>
    if seen.contains n then waitingDependencies env targets directAdmissions rest seen found
    else
      let seen := seen.insert n
      let direct := ((env.find? n).bind (fun ci => ci.value? true)).any
        (fun value => value.getUsedConstants.contains `sorryAx)
      let found := if (if directAdmissions then direct else targets.contains n)
        then n :: found else found
      let deps := match env.find? n with
        | none => []
        | some ci => ci.type.getUsedConstants.toList ++
            ((ci.value? true).map (fun v => v.getUsedConstants.toList)).getD []
      waitingDependencies env targets directAdmissions (deps ++ rest) seen found
elab "#waiting_dependencies " n:ident : command => do
  let env ← getEnv
  let name := n.getId
  unless (env.find? name).isSome do throwError "Missing audit entry {name}"
  let targets := [
    `ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unpark2_run,
    `ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_run,
    `ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_releaseZero,
    `ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_run,
    `ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_releaseZero,
    `ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6_run,
    `ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6_releaseZero]
  let deps := waitingDependencies env targets false [name]
  let admitted := waitingDependencies env targets true [name]
  liftIO <| IO.println ("WAITING_DEPS " ++ name.toString ++ " : " ++
    String.intercalate "," (deps.map Name.toString))
  liftIO <| IO.println ("ADMITTED_DEPS " ++ name.toString ++ " : " ++
    String.intercalate "," (admitted.map Name.toString))
elab "#waiting_prop " n:ident : command => do
  let env ← getEnv
  let some info := env.find? n.getId | throwError "Missing proof"
  let isProof ← liftTermElabM <| Meta.isProp info.type
  unless isProof do throwError "Waiting entry must have a Prop type: {n.getId}"
#waiting_prop ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unpark2_run
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unparkRecords2
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unparkRecords2
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unparkPre2
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unparkPre2
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unparkPhaseDebt2
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unparkPhaseDebt2
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unparkRecords2_actualCursor
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unparkRecords2_actualCursor
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unparkRecords2_nonempty
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unparkRecords2_nonempty
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unpark2_wellFormed
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unpark2_wellFormed
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unpark2_support
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unpark2_support
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unpark2_run
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unpark2_run
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unpark2
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unpark2
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unparkRule2
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.unparkRule2

#waiting_prop ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_run
#waiting_prop ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_releaseZero
#waiting_prop ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_run
#waiting_prop ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_releaseZero
#waiting_prop ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6_run
#waiting_prop ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6_releaseZero
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2Prefix
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2Prefix
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2Tail
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2Tail
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2Legal
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2Legal
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2PhaseDebt
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2PhaseDebt
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_program_eq
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_program_eq
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_legal_start
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_legal_start
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_wellFormed
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_wellFormed
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_support
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_support
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_run
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_run
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_releaseZero
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward2_releaseZero
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6Prefix
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6Prefix
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6Tail
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6Tail
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6Legal
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6Legal
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6PhaseDebt
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6PhaseDebt
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_program_eq
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_program_eq
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_legal_start
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_legal_start
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_wellFormed
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_wellFormed
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_support
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_support
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_run
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_run
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_releaseZero
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.forward6_releaseZero
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.eraseRecords6
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.eraseRecords6
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erasePre6
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erasePre6
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erasePhaseDebt6
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erasePhaseDebt6
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.eraseRecords6_actual
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.eraseRecords6_actual
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6_wellFormed
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6_wellFormed
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6_support
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6_support
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6_run
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6_run
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.eraseRule6
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.eraseRule6
#print axioms ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6_releaseZero
#waiting_dependencies ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer.erase6_releaseZero
