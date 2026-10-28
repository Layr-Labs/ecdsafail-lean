import ECDSAAdd.Arithmetic.Paper935.HmrSourceGapInput
import ECDSAAdd.Arithmetic.Paper935.HmrSourceGapPhase
import ECDSAAdd.Arithmetic.Paper935.HmrSourceSignInput

namespace ECDSAAdd.Arithmetic.Paper935
attribute [local irreducible] s2ForwardProgram s6ForwardProgram s6EraseProgram
  s2SourceGap s6SourceGap s2HmrSourceUnpark

def hmrSourceS2Lifecycle : RecordedProgram :=
  s2ForwardProgram++s2SourceGap++s2HmrSourceUnpark

def hmrSourceS6Lifecycle : RecordedProgram :=
  s6ForwardProgram++s6SourceGap++s6EraseProgram

def hmrSourceThreeCall (J : RecordedProgram) : RecordedProgram :=
  (hmrSourceS2Lifecycle++J)++hmrSourceS6Lifecycle

/-- Source-fixed call and gap programs. The unknown producer certificates,
record conditions and actual intervening J remain explicit. The caller no
longer assumes whole-gap frame or demolition facts. -/
theorem hmrSourceThreeCall_phase (J : RecordedProgram)
    (forward2 : HmrRowMulSpec s2HmrSourceLayout s2ForwardProgram)
    (unpark : HmrRowUnparkSpec s2HmrSourceLayout s2HmrSourceUnpark)
    (unparkRule : HmrUnparkInputRule s2HmrSourceLayout s2HmrSourceUnpark unpark)
    (forward6 : HmrRowMulSpec s6HmrSourceLayout s6ForwardProgram)
    (erase : HmrRowMulInvSpec s6HmrSourceLayout s6EraseProgram)
    (eraseRule : HmrEraseInputRule s6HmrSourceLayout s6EraseProgram erase)
    (call2 call6 : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal2 : forward2.legalCursor cursor) (pre2 : HmrRowMulPre s2HmrSourceLayout call2 s)
    (records2 : unparkRule.records tape cursor
      (cursor+recordedMeasurementCount (s2ForwardProgram++s2SourceGap)))
    (legal6 : forward6.legalCursor (cursor+recordedMeasurementCount (hmrSourceS2Lifecycle++J)))
    (pre6 : HmrRowMulPre s6HmrSourceLayout call6
      (runWithTape (hmrSourceS2Lifecycle++J) tape cursor s))
    (records6 : eraseRule.records tape (cursor+recordedMeasurementCount (hmrSourceS2Lifecycle++J))
      (cursor+recordedMeasurementCount (hmrSourceS2Lifecycle++J)+
        recordedMeasurementCount (s6ForwardProgram++s6SourceGap))) :
    (runWithTape (hmrSourceThreeCall J) tape cursor s).phase =
      xor s.phase (hmrThreeCallDebt s2ForwardProgram s2SourceGap s2HmrSourceUnpark J
        s6ForwardProgram s6SourceGap forward2.rowMulPhaseDebt unpark.phaseDebt
        forward6.rowMulPhaseDebt erase.phaseDebt tape cursor s) := by
  exact hmr_three_call_phase _ _ _ _ _ J _ _ _ forward2 unpark forward6 erase call2 call6 s tape cursor
    legal2 pre2
    (s2SourceGap_unpark_input _ _ forward2 unpark unparkRule call2 s tape cursor legal2 pre2 records2)
    legal6 pre6
    (s6SourceGap_erase_input _ _ forward6 erase eraseRule call6 _ tape _ legal6 pre6 records6)

end ECDSAAdd.Arithmetic.Paper935
