import ECDSAAdd.Arithmetic.RecordedRailCarryProgram
import ECDSAAdd.Arithmetic.RecordedCarryPhaseProof
import ECDSAAdd.Framework.WireRename

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailCarry

/-- The literal compute leaves dressed inputs and the arithmetic carry.
It has no measurement and preserves arbitrary phase and every spectator. -/
theorem carryStep_some (a b p carry : Wire) (nd : [a,b,p,carry].Nodup)
    (s : State) (m : List Bool) (hc : s.basis carry=false) :
    run (carryStep a b (some p) carry) m s=
      ⟨s.phase,writeBit (writeBit (writeBit s.basis a (s.basis a ^^ s.basis p))
        b (s.basis b ^^ s.basis p)) carry (carryValue a b (some p) s.basis)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hap,hac⟩,⟨hbp,hbc⟩,hpc⟩ := nd
  have hba := Ne.symm hab
  have hpa := Ne.symm hap
  have hca := Ne.symm hac
  have hpb := Ne.symm hbp
  have hcb := Ne.symm hbc
  have hcp := Ne.symm hpc
  simp only [carryStep,run]
  apply State.extensionality
  · rfl
  · funext q
    by_cases ha : q=a <;> by_cases hb : q=b <;> by_cases hp : q=p <;> by_cases hk : q=carry <;>
      simp_all [carryValue,writeBit,Function.update]

/-- The source's fresh HMR and immediate CZ repair each other after undressing
the arithmetic carry. The original input rail and carry-in are restored. -/
theorem unwindStep_some (a b p carry : Wire) (nd : [a,b,p,carry].Nodup)
    (s : State) (m : List Bool)
    (hc : s.basis carry=((s.basis a && s.basis b) ^^ s.basis p)) :
    run (unwindStep a b (some p) carry) m s=
      ⟨s.phase,writeBit (writeBit (writeBit s.basis carry false)
        a (s.basis a ^^ s.basis p)) b (s.basis b ^^ (s.basis a ^^ s.basis p))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hap,hac⟩,⟨hbp,hbc⟩,hpc⟩ := nd
  have hba := Ne.symm hab
  have hpa := Ne.symm hap
  have hca := Ne.symm hac
  have hpb := Ne.symm hbp
  have hcb := Ne.symm hbc
  have hcp := Ne.symm hpc
  simp only [unwindStep,run]
  apply State.extensionality
  · cases ha : s.basis a <;> cases hb : s.basis b <;> cases hp : s.basis p <;>
      cases hm : m.headD false <;> cases hs : s.phase <;>
      simp_all [measureAndCorrect,ECDSAAdd.correct,writeBit,Function.update]
  · funext q
    by_cases ha : q=a <;> by_cases hb : q=b <;> by_cases hp : q=p <;> by_cases hk : q=carry <;>
      cases hm : m.headD false <;> simp_all [measureAndCorrect,ECDSAAdd.correct,writeBit,Function.update]

/-- Old-record correction repairs incoming debt before the source's independent
fresh MX. The result includes every basis bit, not only the output sum. -/
theorem retire_some (a b p carry : Wire) (nd : [a,b,p,carry].Nodup)
    (bits : BasisState) (phase : Bool) (m : List Bool) (oldOrdinal cursor : Nat)
    (hc : bits carry=((bits a && bits b) ^^ bits p)) :
    runWithTape (retire a b (some p) carry oldOrdinal) m cursor
      ⟨phase ^^ (m.getD oldOrdinal false && bits carry),bits⟩=
      ⟨phase,writeBit (writeBit (writeBit bits carry false)
        a (bits a ^^ bits p)) b (bits b ^^ (bits a ^^ bits p))⟩ := by
  simp only [retire,runWithTape_append,recordedMeasurementCount,Nat.add_zero]
  rw [RecordedCarryPhase.recorded_Z_cancel phase (bits carry) m oldOrdinal cursor bits carry rfl,
    runWithTape_embedRecorded]
  exact unwindStep_some a b p carry nd ⟨phase,bits⟩ (m.drop cursor) hc

/-- Actual compute/recompute plus old-record correction and normal unwind.
The incoming debt is oldm times the arithmetic carry, not the fresh MX bit. -/
theorem correct_some (a b p carry : Wire) (nd : [a,b,p,carry].Nodup)
    (bits : BasisState) (phase : Bool) (m : List Bool) (oldOrdinal cursor : Nat)
    (hc : bits carry=false) :
    runWithTape (program a b (some p) carry oldOrdinal) m cursor
      ⟨phase ^^ (m.getD oldOrdinal false && carryValue a b (some p) bits),bits⟩=
      ⟨phase,writeBit bits b ((bits b ^^ bits a) ^^ bits p)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hap,hac⟩,⟨hbp,hbc⟩,hpc⟩ := nd
  have hba := Ne.symm hab
  have hpa := Ne.symm hap
  have hca := Ne.symm hac
  have hpb := Ne.symm hbp
  have hcb := Ne.symm hbc
  have hcp := Ne.symm hpc
  simp only [program,retire,runWithTape_append,recordedMeasurementCount_append,
    carry_measurements,recordedMeasurementCount,Nat.add_zero]
  simp only [runWithTape_embedRecorded,runWithTape_phaseFromRecord]
  apply State.extensionality
  · cases ha : bits a <;> cases hb : bits b <;> cases hp : bits p <;>
      cases ho : m.getD oldOrdinal false <;> cases hf : (m.drop cursor).headD false <;>
      cases hphase : phase <;>
      simp_all [carryStep,unwindStep,run,measureAndCorrect,ECDSAAdd.correct,
        carryValue,writeBit,Function.update]
  · funext q
    by_cases hqa : q=a <;> by_cases hqb : q=b <;> by_cases hqp : q=p <;> by_cases hqc : q=carry <;>
      cases ha : bits a <;> cases hb : bits b <;> cases hp : bits p <;>
      cases ho : m.getD oldOrdinal false <;> cases hf : (m.drop cursor).headD false <;>
      simp_all [carryStep,unwindStep,run,measureAndCorrect,ECDSAAdd.correct,
        carryValue,writeBit,Function.update]

theorem unwindStep_none (a b carry : Wire) (nd : [a,b,carry].Nodup)
    (s : State) (m : List Bool) (hc : s.basis carry=(s.basis a && s.basis b)) :
    run (unwindStep a b none carry) m s=
      ⟨s.phase,writeBit (writeBit s.basis carry false) b (s.basis b ^^ s.basis a)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac⟩,hbc⟩ := nd
  have hba := Ne.symm hab
  have hca := Ne.symm hac
  have hcb := Ne.symm hbc
  simp only [unwindStep,run]
  apply State.extensionality
  · cases ha : s.basis a <;> cases hb : s.basis b <;> cases hm : m.headD false <;>
      cases hs : s.phase <;> simp_all [measureAndCorrect,ECDSAAdd.correct,writeBit,Function.update]
  · funext q
    by_cases ha : q=a <;> by_cases hb : q=b <;> by_cases hk : q=carry <;>
      cases hm : m.headD false <;> simp_all [measureAndCorrect,ECDSAAdd.correct,writeBit,Function.update]

theorem retire_none (a b carry : Wire) (nd : [a,b,carry].Nodup)
    (bits : BasisState) (phase : Bool) (m : List Bool) (oldOrdinal cursor : Nat)
    (hc : bits carry=(bits a && bits b)) :
    runWithTape (retire a b none carry oldOrdinal) m cursor
      ⟨phase ^^ (m.getD oldOrdinal false && bits carry),bits⟩=
      ⟨phase,writeBit (writeBit bits carry false) b (bits b ^^ bits a)⟩ := by
  simp only [retire,runWithTape_append,recordedMeasurementCount,Nat.add_zero]
  rw [RecordedCarryPhase.recorded_Z_cancel phase (bits carry) m oldOrdinal cursor bits carry rfl,
    runWithTape_embedRecorded]
  exact unwindStep_none a b carry nd ⟨phase,bits⟩ (m.drop cursor) hc

theorem correct_none (a b carry : Wire) (nd : [a,b,carry].Nodup)
    (bits : BasisState) (phase : Bool) (m : List Bool) (oldOrdinal cursor : Nat)
    (hc : bits carry=false) :
    runWithTape (program a b none carry oldOrdinal) m cursor
      ⟨phase ^^ (m.getD oldOrdinal false && carryValue a b none bits),bits⟩=
      ⟨phase,writeBit bits b (bits b ^^ bits a)⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac⟩,hbc⟩ := nd
  have hba := Ne.symm hab
  have hca := Ne.symm hac
  have hcb := Ne.symm hbc
  simp only [program,retire,runWithTape_append,recordedMeasurementCount_append,
    carry_measurements,recordedMeasurementCount,Nat.add_zero]
  simp only [runWithTape_embedRecorded,runWithTape_phaseFromRecord]
  apply State.extensionality
  · cases ha : bits a <;> cases hb : bits b <;> cases ho : m.getD oldOrdinal false <;>
      cases hf : (m.drop cursor).headD false <;> cases hphase : phase <;>
      simp_all [carryStep,unwindStep,run,measureAndCorrect,ECDSAAdd.correct,
        carryValue,writeBit,Function.update]
  · funext q
    by_cases hqa : q=a <;> by_cases hqb : q=b <;> by_cases hqc : q=carry <;>
      cases ha : bits a <;> cases hb : bits b <;> cases ho : m.getD oldOrdinal false <;>
      cases hf : (m.drop cursor).headD false <;>
      simp_all [carryStep,unwindStep,run,measureAndCorrect,ECDSAAdd.correct,
        carryValue,writeBit,Function.update]

theorem exit_clean_some (a b p carry : Wire) (nd : [a,b,p,carry].Nodup)
    (bits : BasisState) (phase : Bool) (m : List Bool) (oldOrdinal cursor : Nat)
    (hc : bits carry=false) :
    (runWithTape (program a b (some p) carry oldOrdinal) m cursor
      ⟨phase ^^ (m.getD oldOrdinal false && carryValue a b (some p) bits),bits⟩).basis carry=false := by
  rw [correct_some a b p carry nd bits phase m oldOrdinal cursor hc]
  have different : carry ≠ b := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd
    exact Ne.symm nd.2.1.2
  simp [writeBit,Function.update_of_ne different,hc]

theorem quantum_sites_some (a b p carry oldOrdinal : Nat) (nd : [a,b,p,carry].Nodup) :
    (recordedWires (program a b (some p) carry oldOrdinal)).card=4 := by
  rw [(support_some a b p carry oldOrdinal).1]
  simpa using List.toFinset_card_of_nodup nd

theorem quantum_sites_none (a b carry oldOrdinal : Nat) (nd : [a,b,carry].Nodup) :
    (recordedWires (program a b none carry oldOrdinal)).card=3 := by
  rw [(support_none a b carry oldOrdinal).1]
  simpa using List.toFinset_card_of_nodup nd

end ECDSAAdd.Arithmetic.RecordedRailCarry
#print axioms ECDSAAdd.Arithmetic.RecordedRailCarry.carryStep_some
#print axioms ECDSAAdd.Arithmetic.RecordedRailCarry.retire_some
#print axioms ECDSAAdd.Arithmetic.RecordedRailCarry.correct_some
#print axioms ECDSAAdd.Arithmetic.RecordedRailCarry.correct_none
