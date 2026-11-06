import ECDSAAdd.Submission.Entrant.TerminalFiveBridge
import ECDSAAdd.Submission.Entrant.TerminalFivePreTransport
import ECDSAAdd.Submission.Entrant.TerminalFiveShiftedRows
import ECDSAAdd.Submission.Entrant.TerminalFivePlacement

namespace ECDSAAdd.Entrant.TerminalFiveSample
open ECDSAAdd Arithmetic MappedCompressed Challenge CompactCertificates
open TerminalFiveBridge
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run wires

def model (g s : Bool) (uv : Nat×Nat) : State :=
  ⟨false,(run forward [] ⟨false,TerminalFiveDomain.pre g s uv.1 uv.2⟩).basis⟩

theorem model_pull (g s : Bool) (uv : Nat×Nat) :
    pullState perm (model g s uv)=⟨false,MeasuredCodec5.bitsOf (postDense g s uv)⟩ := by
  have start : pullState perm ⟨false,TerminalFiveDomain.pre g s uv.1 uv.2⟩=
      ⟨false,MeasuredCodec5.bitsOf (preDense g s uv)⟩ := TerminalFivePreTransport.pre_pull g s uv
  have eq := ECDSAAdd.run_rename perm perm.injective forwardDense []
    ⟨false,TerminalFiveDomain.pre g s uv.1 uv.2⟩
  rw [forward_placement,start,MeasuredCodec5.run_sim] at eq
  apply State.extensionality
  · rfl
  · have basis := congrArg State.basis eq
    simpa only [model,pullState,Rolling1588.Replay.sim_basis,postDense] using basis

theorem shifted_placement : renameProgram perm TerminalFiveShifted.reference=TerminalFivePlacement.old := by
  decide +kernel

theorem sample_run (g s : Bool) (uv : Nat×Nat) (member : uv∈TerminalFiveDomain.pairs)
    (m n : List Bool) : run physical m (model g s uv)=run TerminalFivePlacement.old n (model g s uv) := by
  have table := inputTable
  simp only [List.all_eq_true] at table
  have row := table uv member
  simp only [checkInput,List.all_eq_true] at row
  have mem := row g (by cases g <;> simp) s (by cases s <;> simp)
  simp only [decide_eq_true_eq] at mem
  have same := TerminalFiveShiftedRows.allRows (postDense g s uv) mem m n
  rw [←shifted_placement]
  unfold physical
  apply pull_injective perm
  rw [ECDSAAdd.run_rename perm perm.injective,ECDSAAdd.run_rename perm perm.injective,model_pull]
  exact same


end ECDSAAdd.Entrant.TerminalFiveSample
