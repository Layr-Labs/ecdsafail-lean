import ECDSAAdd.Arithmetic.Paper935.HmrSourceThreeCall
import ECDSAAdd.Arithmetic.Paper935.FusedEmpiricalBudget

namespace ECDSAAdd.Arithmetic.Paper935
open FailureBudget FiniteUnitary RecordedQuantum
attribute [local irreducible] s2ForwardProgram s6ForwardProgram s6EraseProgram
  s2SourceGap s6SourceGap s2HmrSourceUnpark

variable (J : RecordedProgram)
    (forward2 : HmrRowMulSpec s2HmrSourceLayout s2ForwardProgram)
    (unpark : HmrRowUnparkSpec s2HmrSourceLayout s2HmrSourceUnpark)
    (unparkRule : HmrUnparkInputRule s2HmrSourceLayout s2HmrSourceUnpark unpark)
    (forward6 : HmrRowMulSpec s6HmrSourceLayout s6ForwardProgram)
    (erase : HmrRowMulInvSpec s6HmrSourceLayout s6EraseProgram)
    (eraseRule : HmrEraseInputRule s6HmrSourceLayout s6EraseProgram erase)

/-- Remaining execution obligations for one actual source-shaped call chain.
These are producer/caller premises, not certificates constructed in this file.
The second precondition is on the actual reached state, with cumulative cursor. -/
structure HmrSourceRunConditions (call2 call6 : FusedCall)
    (s : State) (tape : List Bool) (cursor : Nat) : Prop where
  legal2 : forward2.legalCursor cursor
  pre2 : HmrRowMulPre s2HmrSourceLayout call2 s
  records2 : unparkRule.records tape cursor
    (cursor+recordedMeasurementCount (s2ForwardProgram++s2SourceGap))
  legal6 : forward6.legalCursor (cursor+recordedMeasurementCount (hmrSourceS2Lifecycle++J))
  pre6 : HmrRowMulPre s6HmrSourceLayout call6
    (runWithTape (hmrSourceS2Lifecycle++J) tape cursor s)
  records6 : eraseRule.records tape (cursor+recordedMeasurementCount (hmrSourceS2Lifecycle++J))
    (cursor+recordedMeasurementCount (hmrSourceS2Lifecycle++J)+
      recordedMeasurementCount (s6ForwardProgram++s6SourceGap))

/-- Explicit cancellation of the total debt, not separate phase preservation
of each stage. Full basis equality includes every auxiliary and output wire. -/
theorem hmrSource_run_eq (call2 call6 : FusedCall) (s : State)
    (tape : List Bool) (cursor : Nat) (output : BasisState)
    (ready : HmrSourceRunConditions J forward2 unpark unparkRule forward6 erase eraseRule
      call2 call6 s tape cursor)
    (basis : (runWithTape (hmrSourceThreeCall J) tape cursor s).basis = output)
    (cancel : hmrThreeCallDebt s2ForwardProgram s2SourceGap s2HmrSourceUnpark J
      s6ForwardProgram s6SourceGap forward2.rowMulPhaseDebt unpark.phaseDebt
      forward6.rowMulPhaseDebt erase.phaseDebt tape cursor s = false) :
    runWithTape (hmrSourceThreeCall J) tape cursor s = ⟨s.phase, output⟩ := by
  have hp := hmrSourceThreeCall_phase J forward2 unpark unparkRule forward6 erase eraseRule
    call2 call6 s tape cursor ready.legal2 ready.pre2 ready.records2
    ready.legal6 ready.pre6 ready.records6
  rw [cancel, Bool.xor_false] at hp
  exact State.extensionality _ _ hp basis

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
/-- Derive all-tape agreement from the source-specific execution obligations.
No tape distribution or uniform input law is assumed. `bad` is supplied
independently; the caller must prove every premise outside that same event. -/
theorem hmrSource_recordedAgreement (input output : X → BasisState) (bad : Finset X)
    (call2 call6 : X → FusedCall)
    (ready : ∀ x, x ∉ bad → ∀ phase tape,
      HmrSourceRunConditions J forward2 unpark unparkRule forward6 erase eraseRule
        (call2 x) (call6 x) ⟨phase,input x⟩ tape 0)
    (basis : ∀ x, x ∉ bad → ∀ phase tape,
      (runWithTape (hmrSourceThreeCall J) tape 0 ⟨phase,input x⟩).basis = output x)
    (cancel : ∀ x, x ∉ bad → ∀ phase tape,
      hmrThreeCallDebt s2ForwardProgram s2SourceGap s2HmrSourceUnpark J
        s6ForwardProgram s6SourceGap forward2.rowMulPhaseDebt unpark.phaseDebt
        forward6.rowMulPhaseDebt erase.phaseDebt tape 0 ⟨phase,input x⟩ = false) :
    RecordedAgreement (hmrSourceThreeCall J) input output bad := by
  intro x hx phase tape
  exact hmrSource_run_eq J forward2 unpark unparkRule forward6 erase eraseRule
    (call2 x) (call6 x) _ tape 0 _ (ready x hx phase tape)
    (basis x hx phase tape) (cancel x hx phase tape)

/-- Conditional quantum error for the SAME program and original-label bad set.
The circuit equality prevents substituting an unrelated legal circuit. The
empirical population bounds remain assumptions, never inferred from counts.
See `docs/ASSUMPTIONS_B5.md` for both empirical-bound and input-law assumptions. -/
theorem hmrSource_empirical_error {n l : Nat} (c : Circuit n 0 l)
    (program_eq : c.program = hmrSourceThreeCall J)
    (ι : X ↪ Bits n) (idealOp : X ≃ X) (μ : InputLaw X)
    (events : FailureEvents X) (scaling : Finset X) (calls : X → List FusedCall)
    (b : EmpiricalBudget μ events scaling calls) (hlt : b.bounds.total < 1)
    (call2 call6 : X → FusedCall)
    (ready : ∀ x, x ∉ scalingBad events scaling ∪ (fusedFailures calls).bad → ∀ phase tape,
      HmrSourceRunConditions J forward2 unpark unparkRule forward6 erase eraseRule
        (call2 x) (call6 x) ⟨phase,extend (ι x)⟩ tape 0)
    (basis : ∀ x, x ∉ scalingBad events scaling ∪ (fusedFailures calls).bad → ∀ phase tape,
      (runWithTape (hmrSourceThreeCall J) tape 0 ⟨phase,extend (ι x)⟩).basis =
        extend (ι (idealOp x)))
    (cancel : ∀ x, x ∉ scalingBad events scaling ∪ (fusedFailures calls).bad → ∀ phase tape,
      hmrThreeCallDebt s2ForwardProgram s2SourceGap s2HmrSourceUnpark J
        s6ForwardProgram s6SourceGap forward2.rowMulPhaseDebt unpark.phaseDebt
        forward6.rowMulPhaseDebt erase.phaseDebt tape 0 ⟨phase,extend (ι x)⟩ = false)
    (ψ : EuclideanSpace ℂ (Bits n)) (hn : ‖ψ‖=1)
    (matching : ∀ x, ‖ψ x‖^2=(μ.push ι).weight x) :
    ‖actual c ψ-ideal l (encodedPerm ι idealOp) ψ‖ ≤ 2*Real.sqrt b.bounds.total := by
  apply empirical_error c ι idealOp μ events scaling calls b hlt _ ψ hn matching
  rw [program_eq]
  exact hmrSource_recordedAgreement J forward2 unpark unparkRule forward6 erase eraseRule
    _ _ _ call2 call6 ready basis cancel

end ECDSAAdd.Arithmetic.Paper935
