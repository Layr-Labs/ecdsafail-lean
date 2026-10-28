import ECDSAAdd.Arithmetic.Paper935.FusedRepackedInput
import ECDSAAdd.Arithmetic.Paper935.FusedPlacedBorrow
import ECDSAAdd.Arithmetic.Paper935.BorrowGeometry

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Abstract physical views, not a certificate that the HMR compiler reaches
these addresses. Extra comparison/flag scratch is named separately from anc. -/
structure HmrRowMulLayout where
  row : WindowRow
  y : List Wire
  out : List Wire
  anc : List Wire
  flags : Finset Wire
  row_length : row.payload.length=280
  y_length : y.length=256
  out_length : out.length=256
  anc_length : anc.length=24
  distinct : (row.sign::row.payload++y++out++anc).Nodup
  flags_separate : Disjoint flags (row.sign::row.payload++y++out).toFinset

def HmrRowMulLayout.data (L : HmrRowMulLayout) : Finset Wire :=
  (L.row.sign::L.row.payload++L.y++L.out).toFinset

def HmrRowMulLayout.scratch (L : HmrRowMulLayout) : Finset Wire :=
  L.anc.toFinset∪L.flags

def HmrRowMulLayout.support (L : HmrRowMulLayout) : Finset Wire := L.data∪L.scratch

def HmrRowMulLayout.lift (L : HmrRowMulLayout) : Program :=
  placedMagnitude (fusedPlacementMap (L.row.sign::L.row.payload++L.anc)) false

def HmrRowMulLayout.fold (L : HmrRowMulLayout) : Program :=
  placedRowFold (fusedPlacementMap (fusedFoldPlacement L.row.payload L.out L.anc)) false

/-- The parked representation is defined by executing the two existing blocks,
with the same absolute tape cursor as the entire call. It is not the input row. -/
def HmrRowMulLayout.parked (L : HmrRowMulLayout) (tape : List Bool)
    (cursor : Nat) (s : State) : State :=
  runWithTape (embedRecorded (L.lift++L.fold)) tape cursor s

structure HmrRowMulInputs (L : HmrRowMulLayout) (call : FusedCall) (s : State) : Prop where
  multiplier : regValue L.y s.basis=call.multiplier
  output_zero : ∀q∈L.out,s.basis q=false
  scratch_zero : ∀q∈L.scratch,s.basis q=false
  lift_good : call.LiftGood
  row_good : call.RowGood
  horner_good : call.HornerGood

structure HmrRowMulPre (L : HmrRowMulLayout) (call : FusedCall) (s : State) : Prop
    extends HmrRowMulInputs L call s where
  coefficient : L.row.value s.basis=call.coefficient

/-- The phase-debt function is part of the producer's certificate. Its equation
must be proved for actual execution; the caller never supplies an arbitrary
phase-correctness hypothesis. No concrete instance is asserted here. -/
structure HmrRowMulSpec (L : HmrRowMulLayout) (H : RecordedProgram) where
  actualPrefix : RecordedProgram
  scanAndHalves : RecordedProgram
  program_eq : H=actualPrefix++scanAndHalves
  legalCursor : Nat → Prop
  prefix_run : ∀tape cursor s, legalCursor cursor →
    runWithTape actualPrefix tape cursor s =
      runWithTape (embedRecorded (L.lift++L.fold)) tape cursor s
  prefix_measurements : recordedMeasurementCount actualPrefix =
    recordedMeasurementCount (embedRecorded (L.lift++L.fold))
  wellFormed : ∀cursor,legalCursor cursor → RecordedWellFormedAt cursor H
  support : recordedWires H⊆L.support
  rowMulPhaseDebt : List Bool → Nat → State → Bool
  run : ∀call s tape cursor,legalCursor cursor → HmrRowMulPre L call s →
    let result := runWithTape H tape cursor s
    regValue L.out result.basis=call.beforeSign ∧
    (∀q∈L.y,result.basis q=s.basis q) ∧
    result.basis L.row.sign=s.basis L.row.sign ∧
    (∀q∈L.row.payload,result.basis q=(L.parked tape cursor s).basis q) ∧
    (∀q∈L.scratch,result.basis q=false) ∧
    result.phase=xor s.phase (rowMulPhaseDebt tape cursor s)

/-- An inverse-call certificate with an explicit lifecycle relation to the
original signed input. Its premise must be established by the s6 caller. -/
structure HmrRowMulInvSpec (L : HmrRowMulLayout) (R : RecordedProgram) where
  pre : FusedCall → State → List Bool → Nat → State → Prop
  wellFormed : ∀call original tape cursor s,pre call original tape cursor s →
    RecordedWellFormedAt cursor R
  support : recordedWires R⊆L.support
  phaseDebt : List Bool → Nat → State → Bool
  run : ∀call original s tape cursor,pre call original tape cursor s →
    let result := runWithTape R tape cursor s
    (∀q∈L.row.wires,result.basis q=original.basis q) ∧
    (∀q∈L.y,result.basis q=s.basis q) ∧
    (∀q∈L.out,result.basis q=false) ∧
    (∀q∈L.scratch,result.basis q=false) ∧
    result.phase=xor s.phase (phaseDebt tape cursor s)

/-- Unpark borrows the demolished multiplier word, preserving the output.
This is a distinct obligation from inverse row multiplication. -/
structure HmrRowUnparkSpec (L : HmrRowMulLayout) (U : RecordedProgram) where
  pre : FusedCall → State → List Bool → Nat → State → Prop
  wellFormed : ∀call original tape cursor s,pre call original tape cursor s →
    RecordedWellFormedAt cursor U
  support : recordedWires U⊆L.support
  phaseDebt : List Bool → Nat → State → Bool
  run : ∀call original s tape cursor,pre call original tape cursor s →
    let result := runWithTape U tape cursor s
    (∀q∈L.row.wires,result.basis q=original.basis q) ∧
    (∀q∈L.y,result.basis q=false) ∧
    (∀q∈L.out,result.basis q=s.basis q) ∧
    (∀q∈L.scratch,result.basis q=false) ∧
    result.phase=xor s.phase (phaseDebt tape cursor s)

end ECDSAAdd.Arithmetic.Paper935
