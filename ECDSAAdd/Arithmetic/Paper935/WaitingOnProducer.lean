import ECDSAAdd.Arithmetic.Paper935.HmrSourceDataFacts
import ECDSAAdd.Arithmetic.Paper935.HmrUnparkData
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulPrefixLayout
import ECDSAAdd.Arithmetic.Paper935.HmrSourceCallPorts
import ECDSAAdd.Arithmetic.Paper935.HmrLifecycleInput
import ECDSAAdd.Arithmetic.Paper935.HmrRowMulSourcePrograms

namespace ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer

attribute [local irreducible] placedRowFold placedMagnitude s2HmrSourceLayout
  s2HmrSourceUnpark

/-- Producer data confirmed by Lamport db355cbb. Short/empty tapes are supported
by the interpreter; this condition orders absolute cursors only. -/
def unparkRecords2 (_tape : List Bool) (start cursor : Nat) : Prop :=
  start ≤ cursor

/-- Explicit lifecycle premise, not the desired execution conclusion.
Producer confirmation: d55887e4 and data expression db355cbb; task #50. -/
def unparkPre2 (call : FusedCall) (original : State)
    (tape : List Bool) (cursor : Nat) (current : State) : Prop :=
  HmrRowMulPre s2HmrSourceLayout call original ∧
  ∃ start, unparkRecords2 tape start cursor ∧
    HmrUnparkBoundary s2HmrSourceLayout original tape start current

/-- U2 preserves its own input phase. This does not discharge earlier K2 debt.
Producer data confirmation: db355cbb. -/
def unparkPhaseDebt2 (_tape : List Bool) (_cursor : Nat) (_current : State) : Bool :=
  false

theorem unparkRecords2_actualCursor (tape : List Bool) (start count : Nat) :
    unparkRecords2 tape start (start + count) := Nat.le_add_right _ _

theorem unparkRecords2_nonempty (tape : List Bool) (start : Nat) :
    ∃ cursor, unparkRecords2 tape start cursor := ⟨start, Nat.le_refl _⟩

theorem unpark2_wellFormed (cursor : Nat) :
    RecordedWellFormedAt cursor s2HmrSourceUnpark := by
  unfold s2HmrSourceUnpark
  exact embedRecorded_wellFormed _ _

/-- Discharged by finite source-template and layout data certificates. -/
theorem unpark2_support :
    recordedWires s2HmrSourceUnpark ⊆ s2HmrSourceLayout.support := by
  exact s2Unpark_support_checked

/-- TEMPORARY proof obligation. Producer: task #50, Lamport.
Feasibility confirmation: d55887e4; data clarification: db355cbb.
Consumer: PR215. Replace with inverse-fold/inverse-lift execution and transport.
This statement preserves current.phase, not the original pre-K2 phase. -/
theorem unpark2_run (call : FusedCall) (original current : State)
    (tape : List Bool) (cursor : Nat)
    (pre : unparkPre2 call original tape cursor current) :
    let result := runWithTape s2HmrSourceUnpark tape cursor current
    (∀ q ∈ s2HmrSourceLayout.row.wires, result.basis q = original.basis q) ∧
    (∀ q ∈ s2HmrSourceLayout.y, result.basis q = false) ∧
    (∀ q ∈ s2HmrSourceLayout.out, result.basis q = current.basis q) ∧
    (∀ q ∈ s2HmrSourceLayout.scratch, result.basis q = false) ∧
    result.phase = xor current.phase (unparkPhaseDebt2 tape cursor current) := by
  sorry

/-- Assembly only: all data fields are explicit; support is proved and the named
run obligation above remains admitted. Producer task #50; d55887e4; consumer PR215. -/
def unpark2 : HmrRowUnparkSpec s2HmrSourceLayout s2HmrSourceUnpark where
  pre := unparkPre2
  wellFormed := fun _call _original _tape cursor _current _pre =>
    @unpark2_wellFormed cursor
  support := unpark2_support
  phaseDebt := unparkPhaseDebt2
  run := unpark2_run

/-- Direct packaging of the confirmed lifecycle premise; no extra admission.
Producer task #50; d55887e4/db355cbb; consumer PR215. -/
def unparkRule2 : HmrUnparkInputRule s2HmrSourceLayout s2HmrSourceUnpark unpark2 where
  records := unparkRecords2
  accepts := fun _ _ _ start _ _ pre records boundary =>
    ⟨pre, start, records, boundary⟩



attribute [local irreducible] s6HmrSourceLayout
  s2ForwardProgram s6ForwardProgram s6EraseProgram
  s2ForwardUses s6ForwardUses s6EraseUses
  s2ForwardPorts s6ForwardPorts s6ErasePorts
  s2ForwardLifecycle s6ForwardLifecycle s6EraseLifecycle
  rowMulInstantiate


def forward2Prefix : RecordedProgram :=
  (s2ForwardUses.take 2).flatMap (rowMulInstantiate s2ForwardPorts s2ForwardMeasurementStart)

def forward2Tail : RecordedProgram :=
  (s2ForwardUses.drop 2).flatMap (rowMulInstantiate s2ForwardPorts s2ForwardMeasurementStart)

def forward2Legal (cursor : Nat) : Prop := cursor = s2ForwardMeasurementStart

/-- Execution identity only; does not provide cross-call phase cancellation. -/
def forward2PhaseDebt (tape : List Bool) (cursor : Nat) (s : State) : Bool :=
  xor s.phase (runWithTape s2ForwardProgram tape cursor s).phase

theorem forward2_program_eq : s2ForwardProgram = forward2Prefix ++ forward2Tail := by
  unfold s2ForwardProgram forward2Prefix forward2Tail
  rw [← List.flatMap_append, List.take_append_drop]

theorem forward2_legal_start : forward2Legal s2ForwardMeasurementStart := rfl

/-- Discharged by the actual source-prefix semantic equivalence and layout binding. -/
theorem forward2_prefix_run (tape : List Bool) (cursor : Nat) (s : State)
    (_legal : forward2Legal cursor) :
    runWithTape forward2Prefix tape cursor s =
      runWithTape (embedRecorded (s2HmrSourceLayout.lift ++ s2HmrSourceLayout.fold)) tape cursor s := by
  have h := congrArg Prod.fst (s2ForwardPrefix_run ⟨tape, cursor⟩ s)
  rw [s2ForwardPrefix_layout] at h
  exact h

/-- Discharged by the actual source-prefix semantic equivalence and layout binding. -/
theorem forward2_prefix_measurements : recordedMeasurementCount forward2Prefix =
    recordedMeasurementCount (embedRecorded (s2HmrSourceLayout.lift ++ s2HmrSourceLayout.fold)) := by
  have h := s2ForwardPrefix_measurements
  rw [s2ForwardPrefix_layout] at h
  exact h

/-- Discharged by finite source-template and layout data certificates. -/
theorem forward2_wellFormed (cursor : Nat) (_legal : forward2Legal cursor) :
    RecordedWellFormedAt cursor s2ForwardProgram := by
  exact s2Forward_wellFormed_checked cursor

/-- Discharged by finite source-template and layout data certificates. -/
theorem forward2_support : recordedWires s2ForwardProgram ⊆ s2HmrSourceLayout.support := by
  exact s2Forward_support_checked

/-- TEMPORARY Prop proof. Producer Lamport, tasks #49/#50; exact feasibility
confirmation d55887e4 + f27cd75c; PR216 s2ForwardProgram/s6ForwardProgram/
s6EraseProgram; semantic-prefix directive be93ebba; consumer PR215. -/
theorem forward2_run (call : FusedCall) (s : State) (tape : List Bool)
    (cursor : Nat) (_legal : forward2Legal cursor) (_pre : HmrRowMulPre s2HmrSourceLayout call s) :
    let result := runWithTape s2ForwardProgram tape cursor s
    regValue s2HmrSourceLayout.out result.basis = call.beforeSign ∧
    (∀q ∈ s2HmrSourceLayout.y, result.basis q = s.basis q) ∧
    result.basis s2HmrSourceLayout.row.sign = s.basis s2HmrSourceLayout.row.sign ∧
    (∀q ∈ s2HmrSourceLayout.row.payload, result.basis q = (s2HmrSourceLayout.parked tape cursor s).basis q) ∧
    (∀q ∈ s2HmrSourceLayout.scratch, result.basis q = false) ∧
    result.phase = xor s.phase (forward2PhaseDebt tape cursor s) := by
  sorry

def forward2 : HmrRowMulSpec s2HmrSourceLayout s2ForwardProgram where
  actualPrefix := forward2Prefix
  scanAndHalves := forward2Tail
  program_eq := forward2_program_eq
  legalCursor := forward2Legal
  prefix_run := forward2_prefix_run
  prefix_measurements := forward2_prefix_measurements
  wellFormed := forward2_wellFormed
  support := forward2_support
  rowMulPhaseDebt := forward2PhaseDebt
  run := forward2_run

/-- TEMPORARY Prop proof. Producer Lamport, tasks #49/#50; exact feasibility
confirmation d55887e4 + f27cd75c; PR216 s2ForwardProgram/s6ForwardProgram/
s6EraseProgram; semantic-prefix directive be93ebba; consumer PR215. -/
theorem forward2_releaseZero (call : FusedCall) (s : State) (tape : List Bool)
    (cursor : Nat) (_legal : forward2Legal cursor) (_pre : HmrRowMulPre s2HmrSourceLayout call s) :
    RowMulReleaseZero s2ForwardLifecycle
      (fun n => runWithTape (s2ForwardProgram.take n) tape cursor s) := by
  sorry

def forward6Prefix : RecordedProgram :=
  (s6ForwardUses.take 2).flatMap (rowMulInstantiate s6ForwardPorts s6ForwardMeasurementStart)

def forward6Tail : RecordedProgram :=
  (s6ForwardUses.drop 2).flatMap (rowMulInstantiate s6ForwardPorts s6ForwardMeasurementStart)

def forward6Legal (cursor : Nat) : Prop := cursor = s6ForwardMeasurementStart

/-- Execution identity only; does not provide cross-call phase cancellation. -/
def forward6PhaseDebt (tape : List Bool) (cursor : Nat) (s : State) : Bool :=
  xor s.phase (runWithTape s6ForwardProgram tape cursor s).phase

theorem forward6_program_eq : s6ForwardProgram = forward6Prefix ++ forward6Tail := by
  unfold s6ForwardProgram forward6Prefix forward6Tail
  rw [← List.flatMap_append, List.take_append_drop]

theorem forward6_legal_start : forward6Legal s6ForwardMeasurementStart := rfl

/-- Discharged by the actual source-prefix semantic equivalence and layout binding. -/
theorem forward6_prefix_run (tape : List Bool) (cursor : Nat) (s : State)
    (_legal : forward6Legal cursor) :
    runWithTape forward6Prefix tape cursor s =
      runWithTape (embedRecorded (s6HmrSourceLayout.lift ++ s6HmrSourceLayout.fold)) tape cursor s := by
  have h := congrArg Prod.fst (s6ForwardPrefix_run ⟨tape, cursor⟩ s)
  rw [s6ForwardPrefix_layout] at h
  exact h

/-- Discharged by the actual source-prefix semantic equivalence and layout binding. -/
theorem forward6_prefix_measurements : recordedMeasurementCount forward6Prefix =
    recordedMeasurementCount (embedRecorded (s6HmrSourceLayout.lift ++ s6HmrSourceLayout.fold)) := by
  have h := s6ForwardPrefix_measurements
  rw [s6ForwardPrefix_layout] at h
  exact h

/-- Discharged by finite source-template and layout data certificates. -/
theorem forward6_wellFormed (cursor : Nat) (_legal : forward6Legal cursor) :
    RecordedWellFormedAt cursor s6ForwardProgram := by
  exact s6Forward_wellFormed_checked cursor

/-- Discharged by finite source-template and layout data certificates. -/
theorem forward6_support : recordedWires s6ForwardProgram ⊆ s6HmrSourceLayout.support := by
  exact s6Forward_support_checked

/-- TEMPORARY Prop proof. Producer Lamport, tasks #49/#50; exact feasibility
confirmation d55887e4 + f27cd75c; PR216 s2ForwardProgram/s6ForwardProgram/
s6EraseProgram; semantic-prefix directive be93ebba; consumer PR215. -/
theorem forward6_run (call : FusedCall) (s : State) (tape : List Bool)
    (cursor : Nat) (_legal : forward6Legal cursor) (_pre : HmrRowMulPre s6HmrSourceLayout call s) :
    let result := runWithTape s6ForwardProgram tape cursor s
    regValue s6HmrSourceLayout.out result.basis = call.beforeSign ∧
    (∀q ∈ s6HmrSourceLayout.y, result.basis q = s.basis q) ∧
    result.basis s6HmrSourceLayout.row.sign = s.basis s6HmrSourceLayout.row.sign ∧
    (∀q ∈ s6HmrSourceLayout.row.payload, result.basis q = (s6HmrSourceLayout.parked tape cursor s).basis q) ∧
    (∀q ∈ s6HmrSourceLayout.scratch, result.basis q = false) ∧
    result.phase = xor s.phase (forward6PhaseDebt tape cursor s) := by
  sorry

def forward6 : HmrRowMulSpec s6HmrSourceLayout s6ForwardProgram where
  actualPrefix := forward6Prefix
  scanAndHalves := forward6Tail
  program_eq := forward6_program_eq
  legalCursor := forward6Legal
  prefix_run := forward6_prefix_run
  prefix_measurements := forward6_prefix_measurements
  wellFormed := forward6_wellFormed
  support := forward6_support
  rowMulPhaseDebt := forward6PhaseDebt
  run := forward6_run

/-- TEMPORARY Prop proof. Producer Lamport, tasks #49/#50; exact feasibility
confirmation d55887e4 + f27cd75c; PR216 s2ForwardProgram/s6ForwardProgram/
s6EraseProgram; semantic-prefix directive be93ebba; consumer PR215. -/
theorem forward6_releaseZero (call : FusedCall) (s : State) (tape : List Bool)
    (cursor : Nat) (_legal : forward6Legal cursor) (_pre : HmrRowMulPre s6HmrSourceLayout call s) :
    RowMulReleaseZero s6ForwardLifecycle
      (fun n => runWithTape (s6ForwardProgram.take n) tape cursor s) := by
  sorry

def eraseRecords6 (_tape : List Bool) (start cursor : Nat) : Prop :=
  start = s6ForwardMeasurementStart ∧ cursor = s6EraseMeasurementStart

def erasePre6 (call : FusedCall) (original : State)
    (tape : List Bool) (cursor : Nat) (current : State) : Prop :=
  HmrRowMulPre s6HmrSourceLayout call original ∧
  ∃ start, eraseRecords6 tape start cursor ∧
    HmrEraseBoundary s6HmrSourceLayout call original tape start current

/-- Execution identity only; does not provide cross-call phase cancellation. -/
def erasePhaseDebt6 (tape : List Bool) (cursor : Nat) (s : State) : Bool :=
  xor s.phase (runWithTape s6EraseProgram tape cursor s).phase

theorem eraseRecords6_actual (tape : List Bool) :
    eraseRecords6 tape s6ForwardMeasurementStart s6EraseMeasurementStart := ⟨rfl, rfl⟩

/-- Discharged by finite source-template and layout data certificates. -/
theorem erase6_wellFormed (call : FusedCall) (original : State)
    (tape : List Bool) (cursor : Nat) (s : State) (_pre : erasePre6 call original tape cursor s) :
    RecordedWellFormedAt cursor s6EraseProgram := by
  exact s6Erase_wellFormed_checked cursor

/-- Discharged by finite source-template and layout data certificates. -/
theorem erase6_support : recordedWires s6EraseProgram ⊆ s6HmrSourceLayout.support := by
  exact s6Erase_support_checked

/-- TEMPORARY Prop proof. Producer Lamport, tasks #49/#50; exact feasibility
confirmation d55887e4 + f27cd75c; PR216 s2ForwardProgram/s6ForwardProgram/
s6EraseProgram; semantic-prefix directive be93ebba; consumer PR215. -/
theorem erase6_run (call : FusedCall) (original s : State) (tape : List Bool)
    (cursor : Nat) (_pre : erasePre6 call original tape cursor s) :
    let result := runWithTape s6EraseProgram tape cursor s
    (∀q ∈ s6HmrSourceLayout.row.wires, result.basis q = original.basis q) ∧
    (∀q ∈ s6HmrSourceLayout.y, result.basis q = s.basis q) ∧
    (∀q ∈ s6HmrSourceLayout.out, result.basis q = false) ∧
    (∀q ∈ s6HmrSourceLayout.scratch, result.basis q = false) ∧
    result.phase = xor s.phase (erasePhaseDebt6 tape cursor s) := by
  sorry

def erase6 : HmrRowMulInvSpec s6HmrSourceLayout s6EraseProgram where
  pre := erasePre6
  wellFormed := erase6_wellFormed
  support := erase6_support
  phaseDebt := erasePhaseDebt6
  run := erase6_run

def eraseRule6 : HmrEraseInputRule s6HmrSourceLayout s6EraseProgram erase6 where
  records := eraseRecords6
  accepts := fun _ _ _ start _ _ pre records boundary => ⟨pre, start, records, boundary⟩

/-- TEMPORARY Prop proof. Producer Lamport, tasks #49/#50; exact feasibility
confirmation d55887e4 + f27cd75c; PR216 s2ForwardProgram/s6ForwardProgram/
s6EraseProgram; semantic-prefix directive be93ebba; consumer PR215. -/
theorem erase6_releaseZero (call : FusedCall) (original s : State)
    (tape : List Bool) (cursor : Nat) (_pre : erasePre6 call original tape cursor s) :
    RowMulReleaseZero s6EraseLifecycle
      (fun n => runWithTape (s6EraseProgram.take n) tape cursor s) := by
  sorry

end ECDSAAdd.Arithmetic.Paper935.WaitingOnProducer
