import ECDSAAdd.Submission.Entrant.FrontierEntry1591Selected
import ECDSAAdd.Submission.Entrant.FrontierEntry1591Endpoints
import ECDSAAdd.Submission.Entrant.FrontierEntry1591FieldSupport
import ECDSAAdd.Submission.Entrant.ParityField1591

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry1591Field
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots

def controls : List Wire := ParityHost5.payloadControls
  (fun i => OB5.sig 511 (NewHistory5.payloadWire base i))

def work : Wire := base 1797
def host : Wire := base 1543

def entryField : Program :=
  FrontierSW1591.replayS true ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)

def exitField : Program :=
  OwnQ5Endpoint.centerT ++ (HalfFieldOB5.copyN ++ FrontierSW1591.replayS false)

def hosted (P : Program) : Program :=
  [.X (base 511)] ++ (renameProgram HostOB5.hostSwap P ++ [.X (base 511)])

def entryHosted : Program := hosted entryField
def exitHosted : Program := hosted exitField

def entry : Program := ParityField1591.program controls work host entryHosted
def exit : Program := ParityField1591.program controls work host exitHosted

theorem controls_length : controls.length=816 := ParityHost5.payloadControls_length _

theorem controls_member (q : Wire) (h : q∈controls) :
    ∃i,i<816 ∧ OB5.sig 511 (NewHistory5.payloadWire base i)=q := by
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp h
  exact ⟨i,List.mem_range.mp hi,eq⟩

theorem payload_index_bound (i : Nat) (hi : i<816) :
    NewHistory5.payloadWire base i=base (History5.historyId (5*(i/8))
      (NewHistory5.payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩)) ∧
    (History5.historyId (5*(i/8))
      (NewHistory5.payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩)<510 ∨
    (1028≤History5.historyId (5*(i/8))
      (NewHistory5.payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩) ∧
    History5.historyId (5*(i/8))
      (NewHistory5.payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩)<1538)) := by
  refine ⟨rfl,?_⟩
  have hq := (NewHistory5.payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩).isLt
  unfold History5.historyId
  split_ifs <;> omega

theorem host_not_controls : host∉controls := by
  intro used
  obtain ⟨i,hi,eq⟩ := controls_member host used
  have back : OB5.sig 511 (base 1538)=host := by decide +kernel
  have same := OB5.sig_injective 511 (by decide) (eq.trans back.symm)
  rw [(payload_index_bound i hi).1] at same
  have index := base_injective same
  have bound := (payload_index_bound i hi).2
  omega

theorem work_not_controls : work∉controls := by
  intro used
  obtain ⟨i,hi,eq⟩ := controls_member work used
  have back : OB5.sig 511 (base 1797)=work := by decide +kernel
  have same := OB5.sig_injective 511 (by decide) (eq.trans back.symm)
  rw [(payload_index_bound i hi).1] at same
  have index := base_injective same
  have bound := (payload_index_bound i hi).2
  omega

theorem entryHosted_avoids_host : host∉wires entryHosted := by
  apply FrontierFieldSupport1591.hosted_avoids entryField
  have replay := FrontierFieldSupport1591.replay_avoids true
  have copy := FrontierFieldSupport1591.copy_avoids
  have endpoint := FrontierFieldSupport1591.endpoints_avoid.2
  simpa only [entryField,wires_append,Finset.mem_union,not_or] using ⟨replay,copy,endpoint⟩

theorem exitHosted_avoids_host : host∉wires exitHosted := by
  apply FrontierFieldSupport1591.hosted_avoids exitField
  have replay := FrontierFieldSupport1591.replay_avoids false
  have copy := FrontierFieldSupport1591.copy_avoids
  have endpoint := FrontierFieldSupport1591.endpoints_avoid.1
  simpa only [exitField,wires_append,Finset.mem_union,not_or] using ⟨endpoint,copy,replay⟩

theorem entry_run_eq (s : State) (m : List Bool)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis))
    (workIn : s.basis work=false) (workOut : (run entryHosted m s).basis work=false)
    (payload : ∀q∈controls,(run entryHosted m s).basis q=s.basis q) :
    run entry m s=run entryHosted m s :=
  ParityField1591.run_eq controls work host entryHosted s m (by decide)
    host_not_controls entryHosted_avoids_host parity workIn workOut payload

theorem exit_run_eq (s : State) (m : List Bool)
    (parity : s.basis host=TraceParity5.parity (controls.map s.basis))
    (workIn : s.basis work=false) (workOut : (run exitHosted m s).basis work=false)
    (payload : ∀q∈controls,(run exitHosted m s).basis q=s.basis q) :
    run exit m s=run exitHosted m s :=
  ParityField1591.run_eq controls work host exitHosted s m (by decide)
    host_not_controls exitHosted_avoids_host parity workIn workOut payload

end ECDSAAdd.Entrant.FrontierEntry1591Field
