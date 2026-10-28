import ECDSAAdd.Arithmetic.Paper935.HmrRowMulConsumer

namespace ECDSAAdd.Arithmetic.Paper935

/-- Actual Boolean phase change of a recorded segment on its actual input.
This definition is not an assertion that a correction cancels any debt. -/
def hmrPhaseDelta (P : RecordedProgram) (tape : List Bool) (cursor : Nat)
    (s : State) : Bool := xor s.phase (runWithTape P tape cursor s).phase

theorem hmrPhaseDelta_eq (P : RecordedProgram) (tape : List Bool) (cursor : Nat)
    (s : State) : (runWithTape P tape cursor s).phase=xor s.phase (hmrPhaseDelta P tape cursor s) := by
  simp [hmrPhaseDelta]

/-- Relative phase changes compose at the post-state and advanced cursor,
not by applying every segment to the original input or resetting the tape. -/
theorem hmrPhaseDelta_append (P Q : RecordedProgram) (tape : List Bool)
    (cursor : Nat) (s : State) :
    hmrPhaseDelta (P++Q) tape cursor s =
      xor (hmrPhaseDelta P tape cursor s)
        (hmrPhaseDelta Q tape (cursor+recordedMeasurementCount P) (runWithTape P tape cursor s)) := by
  simp only [hmrPhaseDelta,runWithTape_append]
  cases s.phase <;> cases (runWithTape P tape cursor s).phase <;>
    cases (runWithTape Q tape (cursor+recordedMeasurementCount P)
      (runWithTape P tape cursor s)).phase <;> rfl

/-- Three-part debt, with the middle segment interpreted rather than supplied
as an arbitrary Boolean. First and final debts come from producer certificates. -/
def hmrLifecycleDebt (H K : RecordedProgram)
    (forwardDebt restoreDebt : List Bool → Nat → State → Bool)
    (tape : List Bool) (cursor : Nat) (s : State) : Bool :=
  xor (xor (forwardDebt tape cursor s)
    (hmrPhaseDelta K tape (cursor+recordedMeasurementCount H) (runWithTape H tape cursor s)))
    (restoreDebt tape (cursor+recordedMeasurementCount (H++K)) (runWithTape (H++K) tape cursor s))

private theorem lifecycle_phase (H K R : RecordedProgram)
    (forwardDebt restoreDebt : List Bool → Nat → State → Bool)
    (tape : List Bool) (cursor : Nat) (s : State)
    (forward : (runWithTape H tape cursor s).phase=xor s.phase (forwardDebt tape cursor s))
    (restore : (runWithTape (H++K++R) tape cursor s).phase=
      xor (runWithTape (H++K) tape cursor s).phase
        (restoreDebt tape (cursor+recordedMeasurementCount (H++K)) (runWithTape (H++K) tape cursor s))) :
    (runWithTape (H++K++R) tape cursor s).phase=
      xor s.phase (hmrLifecycleDebt H K forwardDebt restoreDebt tape cursor s) := by
  rw [restore]
  have middle := hmrPhaseDelta_eq K tape (cursor+recordedMeasurementCount H)
    (runWithTape H tape cursor s)
  rw [←runWithTape_append] at middle
  rw [middle,forward]
  simp only [hmrLifecycleDebt,Bool.xor_assoc]

theorem s2_hmrLifecycle_phase (L : HmrRowMulLayout) (H K U : RecordedProgram)
    (forward : HmrRowMulSpec L H) (restore : HmrRowUnparkSpec L U)
    (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal : forward.legalCursor cursor) (pre : HmrRowMulPre L call s)
    (unparkInput : restore.pre call s tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s)) :
    (runWithTape (H++K++U) tape cursor s).phase=
      xor s.phase (hmrLifecycleDebt H K forward.rowMulPhaseDebt restore.phaseDebt tape cursor s) := by
  exact lifecycle_phase H K U _ _ tape cursor s
    (forward.run call s tape cursor legal pre).2.2.2.2.2
    (s2_hmrUnpark_consumer L H K U restore call s s tape cursor unparkInput).2.2.2

theorem s6_hmrLifecycle_phase (L : HmrRowMulLayout) (H K R : RecordedProgram)
    (forward : HmrRowMulSpec L H) (restore : HmrRowMulInvSpec L R)
    (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal : forward.legalCursor cursor) (pre : HmrRowMulPre L call s)
    (eraseInput : restore.pre call s tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s)) :
    (runWithTape (H++K++R) tape cursor s).phase=
      xor s.phase (hmrLifecycleDebt H K forward.rowMulPhaseDebt restore.phaseDebt tape cursor s) := by
  exact lifecycle_phase H K R _ _ tape cursor s
    (forward.run call s tape cursor legal pre).2.2.2.2.2
    (s6_hmrErase_consumer L H K R restore call s s tape cursor eraseInput).2.2

/-- The concrete source correction must discharge this equation. No blanket
phase-restoration hypothesis is hidden in a consumer specification. -/
theorem hmrLifecycleDebt_zero_iff (H K : RecordedProgram)
    (forwardDebt restoreDebt : List Bool → Nat → State → Bool)
    (tape : List Bool) (cursor : Nat) (s : State) :
    hmrLifecycleDebt H K forwardDebt restoreDebt tape cursor s=false ↔
    hmrPhaseDelta K tape (cursor+recordedMeasurementCount H) (runWithTape H tape cursor s)=
      xor (forwardDebt tape cursor s)
        (restoreDebt tape (cursor+recordedMeasurementCount (H++K)) (runWithTape (H++K) tape cursor s)) := by
  unfold hmrLifecycleDebt
  cases forwardDebt tape cursor s <;>
    cases hmrPhaseDelta K tape (cursor+recordedMeasurementCount H) (runWithTape H tape cursor s) <;>
    cases restoreDebt tape (cursor+recordedMeasurementCount (H++K)) (runWithTape (H++K) tape cursor s) <;>
    decide

/-- The two lifecycle leases and their intervening caller segment have this
exact combined debt. It is not the XOR of three runs from the original state. -/
theorem hmrPhaseDelta_three (P J Q : RecordedProgram) (tape : List Bool)
    (cursor : Nat) (s : State) :
    hmrPhaseDelta (P++J++Q) tape cursor s=
      xor (xor (hmrPhaseDelta P tape cursor s)
        (hmrPhaseDelta J tape (cursor+recordedMeasurementCount P) (runWithTape P tape cursor s)))
        (hmrPhaseDelta Q tape (cursor+recordedMeasurementCount (P++J))
          (runWithTape (P++J) tape cursor s)) := by
  rw [hmrPhaseDelta_append,hmrPhaseDelta_append]

/-- Exact phase restoration criterion for a recorded segment. -/
theorem hmrPhaseDelta_restored_iff (P : RecordedProgram) (tape : List Bool)
    (cursor : Nat) (s : State) :
    (runWithTape P tape cursor s).phase=s.phase ↔ hmrPhaseDelta P tape cursor s=false := by
  unfold hmrPhaseDelta
  cases s.phase <;> cases (runWithTape P tape cursor s).phase <;> decide

/-- A real deferred Z correction contributes the recorded bit AND the current
recomputed data bit. Record legality remains a separate static obligation. -/
theorem hmrPhaseDelta_recordZ (j : Nat) (q : Wire) (tape : List Bool)
    (cursor : Nat) (s : State) :
    hmrPhaseDelta [.phaseFromRecord j [.Z q]] tape cursor s=
      (tape.getD j false && s.basis q) := by
  simp only [hmrPhaseDelta,runWithTape_phaseFromRecord]
  cases tape.getD j false <;> simp [correct]

/-- The corresponding two-bit phase correction, evaluated on the actual
current state rather than on a stored copy of the original arithmetic input. -/
theorem hmrPhaseDelta_recordCZ (j : Nat) (a b : Wire) (tape : List Bool)
    (cursor : Nat) (s : State) :
    hmrPhaseDelta [.phaseFromRecord j [.CZ a b]] tape cursor s=
      (tape.getD j false && (s.basis a && s.basis b)) := by
  simp only [hmrPhaseDelta,runWithTape_phaseFromRecord]
  cases tape.getD j false <;> simp [correct]

/-- Exact phase-restoration criterion for the s2 lifecycle; no phase-
invariance hypothesis is assumed for the intervening segment. -/
theorem s2_hmrLifecycle_restored_iff (L : HmrRowMulLayout) (H K U : RecordedProgram)
    (forward : HmrRowMulSpec L H) (restore : HmrRowUnparkSpec L U)
    (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal : forward.legalCursor cursor) (pre : HmrRowMulPre L call s)
    (unparkInput : restore.pre call s tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s)) :
    (runWithTape (H++K++U) tape cursor s).phase=s.phase ↔
      hmrLifecycleDebt H K forward.rowMulPhaseDebt restore.phaseDebt tape cursor s=false := by
  rw [s2_hmrLifecycle_phase L H K U forward restore call s tape cursor legal pre unparkInput]
  cases s.phase <;>
    cases hmrLifecycleDebt H K forward.rowMulPhaseDebt restore.phaseDebt tape cursor s <;> decide

/-- Exact phase-restoration criterion for the s6 lifecycle; no phase-
invariance hypothesis is assumed for the intervening segment. -/
theorem s6_hmrLifecycle_restored_iff (L : HmrRowMulLayout) (H K R : RecordedProgram)
    (forward : HmrRowMulSpec L H) (restore : HmrRowMulInvSpec L R)
    (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal : forward.legalCursor cursor) (pre : HmrRowMulPre L call s)
    (eraseInput : restore.pre call s tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s)) :
    (runWithTape (H++K++R) tape cursor s).phase=s.phase ↔
      hmrLifecycleDebt H K forward.rowMulPhaseDebt restore.phaseDebt tape cursor s=false := by
  rw [s6_hmrLifecycle_phase L H K R forward restore call s tape cursor legal pre eraseInput]
  cases s.phase <;>
    cases hmrLifecycleDebt H K forward.rowMulPhaseDebt restore.phaseDebt tape cursor s <;> decide

/-- s2 basis restoration is independent of the phase cancellation criterion:
the original row returns, the demolished multiplier is zero, and output stays. -/
theorem s2_hmrLifecycle_basis (L : HmrRowMulLayout) (H K U : RecordedProgram)
    (restore : HmrRowUnparkSpec L U) (call : FusedCall) (s : State)
    (tape : List Bool) (cursor : Nat)
    (input : restore.pre call s tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s)) :
    (∀q∈L.row.wires,(runWithTape (H++K++U) tape cursor s).basis q=s.basis q) ∧
    (∀q∈L.y,(runWithTape (H++K++U) tape cursor s).basis q=false) ∧
    (∀q∈L.out,(runWithTape (H++K++U) tape cursor s).basis q=
      (runWithTape (H++K) tape cursor s).basis q) := by
  have h := s2_hmrUnpark_consumer L H K U restore call s s tape cursor input
  exact ⟨h.1,h.2.1,h.2.2.1⟩

/-- s6 restores the signed row and erases out. This does not assert phase
restoration; that is exactly the separately stated debt criterion. -/
theorem s6_hmrLifecycle_basis (L : HmrRowMulLayout) (H K R : RecordedProgram)
    (restore : HmrRowMulInvSpec L R) (call : FusedCall) (s : State)
    (tape : List Bool) (cursor : Nat)
    (input : restore.pre call s tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s)) :
    (∀q∈L.row.wires,(runWithTape (H++K++R) tape cursor s).basis q=s.basis q) ∧
    (∀q∈L.out,(runWithTape (H++K++R) tape cursor s).basis q=false) := by
  have h := s6_hmrErase_consumer L H K R restore call s s tape cursor input
  exact ⟨h.1,h.2.1⟩

/-- The complete caller's phase debt. The first and last terms are producer
lifecycle debts; the intervening caller is evaluated on the actual s2 output. -/
def hmrThreeCallDebt (H2 K2 U2 J H6 K6 : RecordedProgram)
    (forward2 restore2 forward6 restore6 : List Bool → Nat → State → Bool)
    (tape : List Bool) (cursor : Nat) (s : State) : Bool :=
  xor (xor (hmrLifecycleDebt H2 K2 forward2 restore2 tape cursor s)
    (hmrPhaseDelta J tape (cursor+recordedMeasurementCount (H2++K2++U2))
      (runWithTape (H2++K2++U2) tape cursor s)))
    (hmrLifecycleDebt H6 K6 forward6 restore6 tape
      (cursor+recordedMeasurementCount ((H2++K2++U2)++J))
      (runWithTape ((H2++K2++U2)++J) tape cursor s))

/-- Compose both concrete producer interfaces into the whole three-call phase
formula. The s6 precondition refers to the actual output of s2 plus J. Neither
local phase restoration nor phase preservation by J is assumed. -/
theorem hmr_three_call_phase
    (L2 L6 : HmrRowMulLayout) (H2 K2 U2 J H6 K6 R6 : RecordedProgram)
    (forward2 : HmrRowMulSpec L2 H2) (unpark : HmrRowUnparkSpec L2 U2)
    (forward6 : HmrRowMulSpec L6 H6) (erase : HmrRowMulInvSpec L6 R6)
    (call2 call6 : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal2 : forward2.legalCursor cursor) (pre2 : HmrRowMulPre L2 call2 s)
    (unparkInput : unpark.pre call2 s tape (cursor+recordedMeasurementCount (H2++K2))
      (runWithTape (H2++K2) tape cursor s))
    (legal6 : forward6.legalCursor (cursor+recordedMeasurementCount ((H2++K2++U2)++J)))
    (pre6 : HmrRowMulPre L6 call6 (runWithTape ((H2++K2++U2)++J) tape cursor s))
    (eraseInput : erase.pre call6 (runWithTape ((H2++K2++U2)++J) tape cursor s) tape
      (cursor+recordedMeasurementCount ((H2++K2++U2)++J)+recordedMeasurementCount (H6++K6))
      (runWithTape (H6++K6) tape (cursor+recordedMeasurementCount ((H2++K2++U2)++J))
        (runWithTape ((H2++K2++U2)++J) tape cursor s))) :
    (runWithTape (((H2++K2++U2)++J)++(H6++K6++R6)) tape cursor s).phase =
      xor s.phase (hmrThreeCallDebt H2 K2 U2 J H6 K6
        forward2.rowMulPhaseDebt unpark.phaseDebt forward6.rowMulPhaseDebt erase.phaseDebt
        tape cursor s) := by
  have first := s2_hmrLifecycle_phase L2 H2 K2 U2 forward2 unpark call2 s tape cursor
    legal2 pre2 unparkInput
  have last := s6_hmrLifecycle_phase L6 H6 K6 R6 forward6 erase call6
    (runWithTape ((H2++K2++U2)++J) tape cursor s) tape
    (cursor+recordedMeasurementCount ((H2++K2++U2)++J)) legal6 pre6 eraseInput
  rw [runWithTape_append, last]
  have middle := hmrPhaseDelta_eq J tape (cursor+recordedMeasurementCount (H2++K2++U2))
    (runWithTape (H2++K2++U2) tape cursor s)
  rw [←runWithTape_append] at middle
  rw [middle,first]
  simp only [hmrThreeCallDebt,Bool.xor_assoc]

/-- Whole-caller cancellation is an equation between the two lifecycle debts
and the actual intervening phase change. It permits cancellation across
segments and does not demand that each lifecycle separately restore phase. -/
theorem hmrThreeCallDebt_zero_iff (H2 K2 U2 J H6 K6 : RecordedProgram)
    (forward2 restore2 forward6 restore6 : List Bool → Nat → State → Bool)
    (tape : List Bool) (cursor : Nat) (s : State) :
    hmrThreeCallDebt H2 K2 U2 J H6 K6 forward2 restore2 forward6 restore6 tape cursor s=false ↔
    hmrPhaseDelta J tape (cursor+recordedMeasurementCount (H2++K2++U2))
      (runWithTape (H2++K2++U2) tape cursor s)=
      xor (hmrLifecycleDebt H2 K2 forward2 restore2 tape cursor s)
        (hmrLifecycleDebt H6 K6 forward6 restore6 tape
          (cursor+recordedMeasurementCount ((H2++K2++U2)++J))
          (runWithTape ((H2++K2++U2)++J) tape cursor s)) := by
  unfold hmrThreeCallDebt
  generalize hmrLifecycleDebt H2 K2 forward2 restore2 tape cursor s = a
  generalize hmrPhaseDelta J tape (cursor+recordedMeasurementCount (H2++K2++U2))
    (runWithTape (H2++K2++U2) tape cursor s) = b
  generalize hmrLifecycleDebt H6 K6 forward6 restore6 tape
    (cursor+recordedMeasurementCount ((H2++K2++U2)++J))
    (runWithTape ((H2++K2++U2)++J) tape cursor s) = c
  cases a <;> cases b <;> cases c <;> decide

/-- Exact whole-caller restoration criterion under the producer interfaces. -/
theorem hmr_three_call_restored_iff
    (L2 L6 : HmrRowMulLayout) (H2 K2 U2 J H6 K6 R6 : RecordedProgram)
    (forward2 : HmrRowMulSpec L2 H2) (unpark : HmrRowUnparkSpec L2 U2)
    (forward6 : HmrRowMulSpec L6 H6) (erase : HmrRowMulInvSpec L6 R6)
    (call2 call6 : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal2 : forward2.legalCursor cursor) (pre2 : HmrRowMulPre L2 call2 s)
    (unparkInput : unpark.pre call2 s tape (cursor+recordedMeasurementCount (H2++K2))
      (runWithTape (H2++K2) tape cursor s))
    (legal6 : forward6.legalCursor (cursor+recordedMeasurementCount ((H2++K2++U2)++J)))
    (pre6 : HmrRowMulPre L6 call6 (runWithTape ((H2++K2++U2)++J) tape cursor s))
    (eraseInput : erase.pre call6 (runWithTape ((H2++K2++U2)++J) tape cursor s) tape
      (cursor+recordedMeasurementCount ((H2++K2++U2)++J)+recordedMeasurementCount (H6++K6))
      (runWithTape (H6++K6) tape (cursor+recordedMeasurementCount ((H2++K2++U2)++J))
        (runWithTape ((H2++K2++U2)++J) tape cursor s))) :
    (runWithTape (((H2++K2++U2)++J)++(H6++K6++R6)) tape cursor s).phase=s.phase ↔
      hmrThreeCallDebt H2 K2 U2 J H6 K6
        forward2.rowMulPhaseDebt unpark.phaseDebt forward6.rowMulPhaseDebt erase.phaseDebt
        tape cursor s=false := by
  rw [hmr_three_call_phase L2 L6 H2 K2 U2 J H6 K6 R6 forward2 unpark forward6 erase
    call2 call6 s tape cursor legal2 pre2 unparkInput legal6 pre6 eraseInput]
  cases s.phase <;>
    cases hmrThreeCallDebt H2 K2 U2 J H6 K6
      forward2.rowMulPhaseDebt unpark.phaseDebt forward6.rowMulPhaseDebt erase.phaseDebt
      tape cursor s <;> decide

end ECDSAAdd.Arithmetic.Paper935
