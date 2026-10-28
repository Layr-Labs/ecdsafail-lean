import ECDSAAdd.Arithmetic.Paper935.HmrSignLifecycle

namespace ECDSAAdd.Arithmetic.Paper935

def hmrRecordedZList (refs : List (Nat × Wire)) : RecordedProgram :=
  refs.map (fun jq => .phaseFromRecord jq.1 [.Z jq.2])

def hmrRecordedZParity : List (Nat × Wire) → List Bool → BasisState → Bool
  | [], _, _ => false
  | (j,q)::rest, tape, bits => xor (tape.getD j false && bits q) (hmrRecordedZParity rest tape bits)

theorem hmrRecordedZList_phase (refs : List (Nat × Wire)) (tape : List Bool)
    (cursor : Nat) (s : State) :
    hmrPhaseDelta (hmrRecordedZList refs) tape cursor s = hmrRecordedZParity refs tape s.basis := by
  induction refs generalizing cursor s with
  | nil => simp [hmrRecordedZList,hmrPhaseDelta,runWithTape,hmrRecordedZParity]
  | cons jq refs ih =>
    obtain ⟨j,q⟩ := jq
    change hmrPhaseDelta ([.phaseFromRecord j [.Z q]]++hmrRecordedZList refs) tape cursor s = _
    rw [hmrPhaseDelta_append,hmrPhaseDelta_recordZ,ih]
    simp only [hmrRecordedZParity,runWithTape_phaseFromRecord]
    cases tape.getD j false <;> simp

/-- Absolute source record numbers; no rebasing to the start of K6. -/
def s6SourceCorrectionRefs : List (Nat × Wire) :=
  (List.range 256).map (fun i => (367502+i,256+i))

theorem s6SourceCorrection_eq : s6SourceCorrection = hmrRecordedZList s6SourceCorrectionRefs := by
  decide +kernel

attribute [local irreducible] s6SourceSign s6SourceUnsign s6SourceCorrection
  s6SourceCorrectionRefs s6SignMap placedSignFix

/-- The sign and inverse-sign routines preserve phase with clean scratch;
therefore the actual gap's phase change is exactly the retained record-Z
parity on the signed intermediate state. It is not assumed to vanish. -/
theorem s6SourceGap_phaseDelta (s : State) (tape : List Bool) (cursor : Nat)
    (clean : ∀i<24,s.basis (s6SignMap (257+i))=false) :
    hmrPhaseDelta s6SourceGap tape cursor s =
      hmrRecordedZParity s6SourceCorrectionRefs tape
        (runWithTape s6SourceSign tape cursor s).basis := by
  let signed := runWithTape s6SourceSign tape cursor s
  let corrected := runWithTape s6SourceCorrection tape
    (cursor+recordedMeasurementCount s6SourceSign) signed
  have first := s6SourceSign_cleanup s tape cursor clean
  have cleanCorrected : ∀i<24,corrected.basis (s6SignMap (257+i))=false := by
    intro i hi
    rw [s6SourceCorrection_basis]
    exact first.1 i hi
  have last : (runWithTape s6SourceUnsign tape
      (cursor+recordedMeasurementCount (s6SourceSign++s6SourceCorrection)) corrected).phase =
      corrected.phase := by
    rw [s6SourceUnsign_run]
    exact (placedSignFix_cleanup _ _ s6SignMap_injective s6SignMap_rowSign_outside true
      corrected _ cleanCorrected).2.2
  have phase : (runWithTape s6SourceGap tape cursor s).phase=corrected.phase := by
    simpa only [s6SourceGap,runWithTape_append] using last
  rw [hmrPhaseDelta,phase]
  have correction := hmrRecordedZList_phase s6SourceCorrectionRefs tape
    (cursor+recordedMeasurementCount s6SourceSign) signed
  rw [←s6SourceCorrection_eq] at correction
  change xor signed.phase corrected.phase = _ at correction
  rw [show signed.phase=s.phase from first.2.2] at correction
  exact correction

/-- Actual post-forward state supplies the clean pool required by the phase
formula; no separate scratch hypothesis is imposed on the caller. -/
theorem s6SourceGap_after_forward_phaseDelta (H : RecordedProgram)
    (forward : HmrRowMulSpec s6HmrSourceLayout H) (call : FusedCall) (s : State)
    (tape : List Bool) (cursor : Nat) (legal : forward.legalCursor cursor)
    (pre : HmrRowMulPre s6HmrSourceLayout call s) :
    hmrPhaseDelta s6SourceGap tape (cursor+recordedMeasurementCount H)
      (runWithTape H tape cursor s) =
    hmrRecordedZParity s6SourceCorrectionRefs tape
      (runWithTape s6SourceSign tape (cursor+recordedMeasurementCount H)
        (runWithTape H tape cursor s)).basis := by
  have h := forward.run call s tape cursor legal pre
  apply s6SourceGap_phaseDelta
  intro i hi
  apply h.2.2.2.2.1
  apply Finset.mem_union_left
  apply List.mem_toFinset.mpr
  change s6SignMap (257+i)∈s6HmrSeamPorts.anc
  rw [←s6SignMap_pool]
  exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩

/-- A concrete parity equation, rather than an assumed phase invariance. -/
theorem s6SourceGap_phase_restored_iff (s : State) (tape : List Bool) (cursor : Nat)
    (clean : ∀i<24,s.basis (s6SignMap (257+i))=false) :
    (runWithTape s6SourceGap tape cursor s).phase=s.phase ↔
      hmrRecordedZParity s6SourceCorrectionRefs tape
        (runWithTape s6SourceSign tape cursor s).basis=false := by
  rw [hmrPhaseDelta_restored_iff,s6SourceGap_phaseDelta s tape cursor clean]

end ECDSAAdd.Arithmetic.Paper935
