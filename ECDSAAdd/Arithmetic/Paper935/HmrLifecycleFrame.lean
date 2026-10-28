import ECDSAAdd.Arithmetic.Paper935.HmrLifecycleInput

namespace ECDSAAdd.Arithmetic.Paper935

/-- Basis mutation targets only; this is NOT quantum support or a census. -/
def hmrBasisWrites : RecordedProgram → Finset Wire
  | [] => ∅
  | .gate (.X q)::P | .gate (.CX _ q)::P | .gate (.CCX _ _ q)::P |
    .gate (.measureX q _ _)::P => insert q (hmrBasisWrites P)
  | .phaseFromRecord _ _::P => hmrBasisWrites P

theorem hmr_preserves_outside_writes (P : RecordedProgram) (tape : List Bool)
    (cursor : Nat) (s : State) (q : Wire) (outside : q∉hmrBasisWrites P) :
    (runWithTape P tape cursor s).basis q=s.basis q := by
  induction P generalizing cursor s with
  | nil => rfl
  | cons i P ih =>
    cases i with
    | gate i =>
      cases i <;> simp only [hmrBasisWrites,Finset.mem_insert,not_or] at outside
      all_goals rw [runWithTape,ih _ _ outside.2]
      all_goals simp [run,measureAndCorrect,writeBit,outside.1]
    | phaseFromRecord j cs =>
      rw [runWithTape,ih _ _ outside]
      split <;> simp

/-- The frame premise used by lifecycle consumers, at the actual H output. -/
theorem hmr_frame_after (H K : RecordedProgram) (kept : Finset Wire)
    (separate : Disjoint kept (hmrBasisWrites K))
    (tape : List Bool) (cursor : Nat) (s : State) :
    ∀q∈kept,(runWithTape (H++K) tape cursor s).basis q=
      (runWithTape H tape cursor s).basis q := by
  intro q hq
  rw [runWithTape_append]
  exact hmr_preserves_outside_writes K tape _ _ q
    (fun hw => Finset.disjoint_left.mp separate hq hw)

/-- Explicit destructive X measurement of a word. Phase debt is retained. -/
def hmrDemolish (qs : List Wire) : RecordedProgram :=
  qs.map (fun q => .gate (.measureX q [] []))

theorem hmrDemolish_basis (qs : List Wire) (tape : List Bool) (cursor : Nat)
    (s : State) (q : Wire) :
    (runWithTape (hmrDemolish qs) tape cursor s).basis q=
      if q∈qs then false else s.basis q := by
  induction qs generalizing cursor s with
  | nil => simp [hmrDemolish,runWithTape]
  | cons a qs ih =>
    change (runWithTape (hmrDemolish qs) tape (cursor+1)
      (measureAndCorrect a [] [] ((tape.drop cursor).headD false) s)).basis q=_
    rw [ih]
    by_cases hq : q∈qs
    · simp [hq]
    · by_cases ha : q=a
      · subst q
        simp [hq,measureAndCorrect,writeBit,correct]
      · simp [hq,ha,measureAndCorrect,writeBit,correct]

/-- Measurements clear their targets on all tapes; later phase corrections
may touch them, but ordinary writes to the demolished word require a proof. -/
theorem hmrDemolish_tail_zero (qs : List Wire) (K : RecordedProgram)
    (separate : Disjoint qs.toFinset (hmrBasisWrites K))
    (tape : List Bool) (cursor : Nat) (s : State) :
    ∀q∈qs,(runWithTape (hmrDemolish qs++K) tape cursor s).basis q=false := by
  intro q hq
  rw [runWithTape_append,hmr_preserves_outside_writes K tape _ _ q
    (fun hw => Finset.disjoint_left.mp separate (List.mem_toFinset.mpr hq) hw)]
  simp [hmrDemolish_basis,hq]

theorem hmrDemolish_writes (qs : List Wire) : hmrBasisWrites (hmrDemolish qs)=qs.toFinset := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simpa [hmrDemolish,hmrBasisWrites] using congrArg (insert q) ih

/-- Concrete demolition-and-correction shape discharges the caller's zero
and frame premises. Matching the source program to this shape is explicit. -/
theorem hmr_unpark_input_of_demolition (L : HmrRowMulLayout)
    (H tail U : RecordedProgram) (forward : HmrRowMulSpec L H)
    (unpark : HmrRowUnparkSpec L U) (rule : HmrUnparkInputRule L U unpark)
    (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal : forward.legalCursor cursor) (pre : HmrRowMulPre L call s)
    (rowFrame : Disjoint ((L.row.sign::L.row.payload).toFinset∪L.scratch)
      (hmrBasisWrites (hmrDemolish L.y++tail)))
    (wordFrame : Disjoint L.y.toFinset (hmrBasisWrites tail))
    (records : rule.records tape cursor
      (cursor+recordedMeasurementCount (H++(hmrDemolish L.y++tail)))) :
    unpark.pre call s tape (cursor+recordedMeasurementCount (H++(hmrDemolish L.y++tail)))
      (runWithTape (H++(hmrDemolish L.y++tail)) tape cursor s) := by
  apply hmr_unpark_input L H (hmrDemolish L.y++tail) U forward unpark rule
    call s tape cursor legal pre
  · exact hmr_frame_after H _ _ rowFrame tape cursor s
  · rw [runWithTape_append]
    exact hmrDemolish_tail_zero L.y tail wordFrame tape _ _
  · exact records

/-- A correction segment with no basis writes to the live call data supplies
the inverse-input frame, even if its phase corrections touch those wires. -/
theorem hmr_erase_input_of_writes (L : HmrRowMulLayout) (H K R : RecordedProgram)
    (forward : HmrRowMulSpec L H) (erase : HmrRowMulInvSpec L R)
    (rule : HmrEraseInputRule L R erase) (call : FusedCall) (s : State)
    (tape : List Bool) (cursor : Nat) (legal : forward.legalCursor cursor)
    (pre : HmrRowMulPre L call s) (frame : Disjoint L.support (hmrBasisWrites K))
    (records : rule.records tape cursor (cursor+recordedMeasurementCount (H++K))) :
    erase.pre call s tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s) := by
  exact hmr_erase_input L H K R forward erase rule call s tape cursor legal pre
    (hmr_frame_after H K L.support frame tape cursor s) records

end ECDSAAdd.Arithmetic.Paper935
