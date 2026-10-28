import ECDSAAdd.Arithmetic.Divsteps.ShallowDecoder
import ECDSAAdd.Framework.RecordedSemantics

namespace ECDSAAdd.Arithmetic.Divsteps

/-- The forward walk may release its branch wire with one bare X measurement.
The caller records the absolute measurement ordinal, not a quantum history bit. -/
def forgetBranch (output : Wire) : RecordedProgram :=
  [.gate (.measureX output [] [])]

theorem forgetBranch_run (output : Wire) (m : List Bool) (k : Nat) (s : State) :
    runWithTape (forgetBranch output) m k s =
      ⟨s.phase ^^ (m.getD k false && s.basis output),
        writeBit s.basis output false⟩ := by
  simp [forgetBranch, runWithTape, run, measureAndCorrect, correct,
    List.getD]

theorem forgetBranch_resources (output : Wire) :
    recordedToffoliCount (forgetBranch output) = 0 ∧
    recordedMeasurementCount (forgetBranch output) = 1 ∧
    recordedWires (forgetBranch output) = {output} := by
  simp [forgetBranch, recordedToffoliCount, recordedMeasurementCount,
    recordedWires, RecordedInstr.quantumWires, Instr.wires,
    toffoliCount, measurementCount, correctionWires]

/-- Recompute a branch only when the reverse walk needs it, then correct the
phase from its earlier measurement. This segment consumes no new outcome
when the decoder is unitary. -/
def recoverBranch (decoder : Program) (output : Wire) (ordinal : Nat) : RecordedProgram :=
  embedRecorded decoder ++ [.phaseFromRecord ordinal [.Z output]]

theorem recoverBranch_run (decoder : Program) (output : Wire) (ordinal : Nat)
    (m : List Bool) (k : Nat) (s : State) (branch : Bool)
    (hdecode : run decoder (m.drop k) s =
      ⟨s.phase, writeBit s.basis output branch⟩) :
    runWithTape (recoverBranch decoder output ordinal) m k s =
      ⟨s.phase ^^ (m.getD ordinal false && branch),
        writeBit s.basis output branch⟩ := by
  rw [recoverBranch, runWithTape_append, runWithTape_embedRecorded, hdecode]
  cases hm : m.getD ordinal false <;>
    simp only [runWithTape, hm] <;> simp [correct, writeBit]

/-- The pending phase from the original measurement cancels for either outcome.
No assumption about proximity of ordinal and cursor is used: another segment
may run in between, provided it establishes the stated decoder/phase contract. -/
theorem recoverBranch_cancel (decoder : Program) (output : Wire) (ordinal : Nat)
    (m : List Bool) (k : Nat) (s : State) (branch phase : Bool)
    (hphase : s.phase = (phase ^^ (m.getD ordinal false && branch)))
    (hdecode : run decoder (m.drop k) s =
      ⟨s.phase, writeBit s.basis output branch⟩) :
    runWithTape (recoverBranch decoder output ordinal) m k s =
      ⟨phase, writeBit s.basis output branch⟩ := by
  rw [recoverBranch_run decoder output ordinal m k s branch hdecode, hphase]
  simp

theorem recoverBranch_resources (decoder : Program) (output : Wire) (ordinal : Nat) :
    recordedToffoliCount (recoverBranch decoder output ordinal) = toffoliCount decoder ∧
    recordedMeasurementCount (recoverBranch decoder output ordinal) = measurementCount decoder ∧
    recordedWires (recoverBranch decoder output ordinal) = wires decoder ∪ {output} ∧
    recordedSources (recoverBranch decoder output ordinal) = {ordinal} := by
  simp [recoverBranch, recordedToffoliCount, recordedMeasurementCount,
    recordedWires, RecordedInstr.quantumWires, correctionWires]
  induction decoder with
  | nil => simp [embedRecorded]
  | cons i p ih => simpa [embedRecorded, recordedSources] using ih

theorem recoverBranch_wellFormed (decoder : Program) (output : Wire) (ordinal k : Nat)
    (h : ordinal < k) : RecordedWellFormedAt k (recoverBranch decoder output ordinal) := by
  rw [recoverBranch, RecordedWellFormedAt_append]
  refine ⟨embedRecorded_wellFormed decoder k, ?_⟩
  simp only [RecordedWellFormedAt, and_true]
  omega

/-- Concrete depth-three reverse decoder and phase correction. The output
wire has been freed by the forward measurement. Inputs encode the branch
at the reverse endpoint; no forward invocation of the decoder is needed. -/
theorem recover3_cancel (flag a b output : Wire)
    (hf : flag ≠ output) (ha : a ≠ output) (hb : b ≠ output)
    (ordinal k : Nat) (m : List Bool) (s : State) (phase : Bool)
    (henable : s.basis flag = true) (hzero : s.basis output = false)
    (hphase : s.phase = (phase ^^ (m.getD ordinal false &&
      (true ^^ s.basis a ^^ s.basis b)))) :
    runWithTape (recoverBranch (decode3 flag a b output) output ordinal) m k s =
      ⟨phase, writeBit s.basis output (true ^^ s.basis a ^^ s.basis b)⟩ := by
  apply recoverBranch_cancel _ _ _ _ _ _ _ _ hphase
  rw [decode3_run flag a b output hf ha hb, henable, hzero]
  simp

/-- The depth-four reverse decoder restores its single scratch and the
borrowed input wires before applying the stored measurement correction. -/
theorem recover4_cancel (w : Fin 9 → Wire) (hw : Function.Injective w)
    (ordinal k : Nat) (m : List Bool) (s : State) (phase branch : Bool)
    (henable : s.basis (w 0) = true) (hzero : s.basis (w 7) = false)
    (h8 : s.basis (w 8) = false)
    (hbranch : branch = (true ^^ s.basis (w 1) ^^ s.basis (w 2) ^^ s.basis (w 3) ^^
      s.basis (w 4) ^^ s.basis (w 5) ^^ s.basis (w 6) ^^
      ((s.basis (w 1) ^^ s.basis (w 2)) && (s.basis (w 4) ^^ s.basis (w 5)))))
    (hphase : s.phase = (phase ^^ (m.getD ordinal false && branch))) :
    runWithTape (recoverBranch (decode4 w) (w 7) ordinal) m k s =
      ⟨phase, writeBit s.basis (w 7) branch⟩ := by
  apply recoverBranch_cancel _ _ _ _ _ _ _ _ hphase
  rw [decode4_run w hw s (m.drop k) h8, henable, hzero, hbranch]
  simp

/-- A complete forward-measure / intervening-program / reverse-recovery pair.
The intervening program may change basis bits and consume measurements. Its
phase and reverse-decoder contracts are explicit: this is not an assumption
that an arbitrary gap is harmless. The absolute source ordinal stays `k`. -/
theorem deferredPair_correct (decoder : Program) (gap : RecordedProgram)
    (output : Wire) (m : List Bool) (k : Nat) (s : State)
    (hphase : (runWithTape gap m (k + 1)
      (runWithTape (forgetBranch output) m k s)).phase =
      (s.phase ^^ (m.getD k false && s.basis output)))
    (hdecode : run decoder (m.drop (k + 1 + recordedMeasurementCount gap))
      (runWithTape gap m (k + 1) (runWithTape (forgetBranch output) m k s)) =
        ⟨(runWithTape gap m (k + 1) (runWithTape (forgetBranch output) m k s)).phase,
          writeBit (runWithTape gap m (k + 1)
            (runWithTape (forgetBranch output) m k s)).basis output (s.basis output)⟩) :
    runWithTape (forgetBranch output ++ gap ++ recoverBranch decoder output k) m k s =
      ⟨s.phase, writeBit
        (runWithTape gap m (k + 1) (runWithTape (forgetBranch output) m k s)).basis
        output (s.basis output)⟩ := by
  simp only [runWithTape_append, recordedMeasurementCount_append,
    forgetBranch, recordedMeasurementCount, measurementCount, Nat.add_zero, Nat.add_assoc] at *
  apply recoverBranch_cancel _ _ _ _ _ _ _ _ hphase hdecode

/-- The pair is a valid recorded module, with the forward measurement
preceding every reference to its ordinal in the recovery segment. -/
theorem deferredPair_wellFormed (decoder : Program) (gap : RecordedProgram)
    (output : Wire) (k : Nat) (hg : RecordedWellFormedAt (k + 1) gap) :
    RecordedWellFormedAt k
      (forgetBranch output ++ gap ++ recoverBranch decoder output k) := by
  rw [RecordedWellFormedAt_append]
  constructor
  · rw [RecordedWellFormedAt_append]
    constructor
    · simp [forgetBranch, RecordedWellFormedAt]
    · simpa [forgetBranch, recordedMeasurementCount, measurementCount] using hg
  · apply recoverBranch_wellFormed
    simp [forgetBranch, recordedMeasurementCount, measurementCount]

/-- After reversing the arithmetic, the restored low input bit clears the
recovered branch. This preserves phase and every non-target bit. -/
theorem clearBranch_run (source output : Wire) (_hne : source ≠ output)
    (s : State) (m : List Bool)
    (h : s.basis output = s.basis source) :
    run [.CX source output] m s = ⟨s.phase, writeBit s.basis output false⟩ := by
  simp [run, h]

end ECDSAAdd.Arithmetic.Divsteps
