import ECDSAAdd.Framework.RecordedSemantics
import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Arithmetic.InPlaceAdder

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedCarryPhase

private def maj (a b cin carry : Wire) : RecordedProgram := embedRecorded (majority a b cin carry)
private def bare (target : Wire) : RecordedProgram := [.gate (.measureX target [] [])]

/-- The clean dummy consumes an independent later outcome. The correction
still names ordinal zero, which measured the original computed carry. -/
def program (a b cin carry dummy : Wire) : RecordedProgram :=
  maj a b cin carry ++ bare carry ++ maj a b cin carry ++ bare dummy ++
    [.phaseFromRecord 0 [.Z carry]] ++ maj a b cin carry

private theorem maj_M (a b cin carry : Wire) : recordedMeasurementCount (maj a b cin carry)=0 := by
  simp [maj,majority,embedRecorded,recordedMeasurementCount,measurementCount]
private theorem bare_M (w : Wire) : recordedMeasurementCount (bare w)=1 := rfl
private theorem phase_M (w : Wire) : recordedMeasurementCount [.phaseFromRecord 0 [.Z w]]=0 := rfl

private theorem maj_run (a b cin carry : Wire) (nd : [a,b,cin,carry].Nodup)
    (m : List Bool) (k : Nat) (s : State) :
    runWithTape (maj a b cin carry) m k s=
      ⟨s.phase,writeBit s.basis carry
        (s.basis carry ^^ carryBit (s.basis a) (s.basis b) (s.basis cin))⟩ := by
  rw [maj,runWithTape_embedRecorded]
  exact majority_correct a b cin carry nd s (m.drop k)

/-- A bare MX stores phase debt against its own outcome and clears only its
measured target. This is an actual gate transition, not a cleanup oracle. -/
theorem bare_measure_debt (target : Wire) (f : Bool) (s : State) (outcome : Bool)
    (hf : s.basis target=f) :
    measureAndCorrect target [] [] outcome s=
      ⟨s.phase ^^ (outcome && f),writeBit s.basis target false⟩ := by
  simp [measureAndCorrect,ECDSAAdd.correct,hf]

private theorem bare_run (target : Wire) (m : List Bool) (k : Nat) (s : State) :
    runWithTape (bare target) m k s=
      ⟨s.phase ^^ ((m.drop k).headD false && s.basis target),writeBit s.basis target false⟩ := by
  simp [bare,runWithTape,run,measureAndCorrect,ECDSAAdd.correct]

private theorem tape_zero (m : List Bool) : (m.drop 0).headD false=m.getD 0 false := by
  cases m <;> rfl

/-- Recomputing the same Boolean permits the old recorded Z to cancel its
phase debt. No condition is placed on a later, independent measurement. -/
theorem deferred_Z_cancel (oldPhase oldOutcome f : Bool) (recomputed : BasisState)
    (target : Wire) (hf : recomputed target=f) :
    (if oldOutcome then ECDSAAdd.correct [.Z target]
      ⟨oldPhase ^^ (oldOutcome && f),recomputed⟩
     else ⟨oldPhase ^^ (oldOutcome && f),recomputed⟩)=⟨oldPhase,recomputed⟩ := by
  cases oldOutcome <;> cases f <;> cases oldPhase <;> simp [ECDSAAdd.correct,hf]

/-- The tape bit is the earlier absolute ordinal, irrespective of the current
cursor or any fresh inverse outcome. The basis remains the recomputed basis. -/
theorem recorded_Z_cancel (oldPhase f : Bool) (m : List Bool) (oldOrdinal cursor : Nat)
    (recomputed : BasisState) (target : Wire) (hf : recomputed target=f) :
    runWithTape [.phaseFromRecord oldOrdinal [.Z target]] m cursor
      ⟨oldPhase ^^ (m.getD oldOrdinal false && f),recomputed⟩=⟨oldPhase,recomputed⟩ := by
  rw [runWithTape_phaseFromRecord]
  exact deferred_Z_cancel oldPhase (m.getD oldOrdinal false) f recomputed target hf

theorem correct (a b cin carry dummy : Wire)
    (nd : [a,b,cin,carry,dummy].Nodup) (s : State) (m : List Bool)
    (hc : s.basis carry=false) (hd : s.basis dummy=false) :
    runWithTape (program a b cin carry dummy) m 0 s=s := by
  have nd4 : [a,b,cin,carry].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd ⊢
    tauto
  have flags := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have hdc : dummy ≠ carry := Ne.symm flags.2.2.2
  simp only [program,runWithTape_append,recordedMeasurementCount_append,
    maj_M,bare_M,phase_M,Nat.add_zero,Nat.zero_add,Nat.reduceAdd]
  simp only [maj_run a b cin carry nd4,bare_run,runWithTape_phaseFromRecord,tape_zero]
  apply State.extensionality
  · cases ha : s.basis a <;> cases hb : s.basis b <;> cases hi : s.basis cin <;>
      cases hm : m.getD 0 false <;> cases hp : s.phase <;>
      simp_all [writeBit,Function.update,carryBit,ECDSAAdd.correct]
  · funext q
    by_cases hq : q=carry
    · subst q
      cases ha : s.basis a <;> cases hb : s.basis b <;> cases hi : s.basis cin <;>
        cases hm : m.getD 0 false <;> simp_all [writeBit,Function.update,carryBit,ECDSAAdd.correct]
    · by_cases hqd : q=dummy
      · subst q
        cases hm : m.getD 0 false <;> simp_all [writeBit,Function.update,ECDSAAdd.correct]
      · cases hm : m.getD 0 false <;> simp_all [writeBit,Function.update,ECDSAAdd.correct]

theorem wellFormed (a b cin carry dummy : Wire) :
    RecordedWellFormedAt 0 (program a b cin carry dummy) := by
  simp [program,maj,bare,majority,embedRecorded,RecordedWellFormedAt,measurementCount]

theorem counts (a b cin carry dummy : Wire) :
    recordedToffoliCount (program a b cin carry dummy)=3 ∧
    recordedMeasurementCount (program a b cin carry dummy)=2 := by
  simp [program,maj,bare,majority,embedRecorded,recordedToffoliCount_append,
    recordedToffoliCount,recordedMeasurementCount,measurementCount,toffoliCount]

/-- This concrete primitive names five quantum sites and one classical source.
Its classical ordinal is not counted as another quantum allocation. -/
theorem support (a b cin carry dummy : Wire) :
    recordedWires (program a b cin carry dummy)={a,b,cin,carry,dummy} ∧
    recordedSources (program a b cin carry dummy)={0} := by
  constructor
  · ext q
    simp [program,maj,bare,majority,embedRecorded,recordedWires,
      RecordedInstr.quantumWires,Instr.wires,correctionWires]
    tauto
  · simp [program,maj,bare,majority,embedRecorded,recordedSources]

theorem quantum_site_count (a b cin carry dummy : Wire)
    (nd : [a,b,cin,carry,dummy].Nodup) :
    (recordedWires (program a b cin carry dummy)).card=5 := by
  have shape : recordedWires (program a b cin carry dummy)=[a,b,cin,carry,dummy].toFinset := by
    rw [(support a b cin carry dummy).1]
    simp
  rw [shape,List.toFinset_card_of_nodup nd]
  rfl

end ECDSAAdd.Arithmetic.RecordedCarryPhase
#print axioms ECDSAAdd.Arithmetic.RecordedCarryPhase.correct
#print axioms ECDSAAdd.Arithmetic.RecordedCarryPhase.recorded_Z_cancel
#print axioms ECDSAAdd.Arithmetic.RecordedCarryPhase.counts
#print axioms ECDSAAdd.Arithmetic.RecordedCarryPhase.support
