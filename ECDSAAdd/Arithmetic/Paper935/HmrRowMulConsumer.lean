import ECDSAAdd.Arithmetic.Paper935.HmrRowMulSpec

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

private theorem row_distinct (L : HmrRowMulLayout) : (L.row.sign::L.row.payload).Nodup := by
  have h := L.distinct
  have h' : ((L.row.sign::L.row.payload)++(L.y++L.out++L.anc)).Nodup := by
    simpa only [List.cons_append,List.append_assoc] using h
  exact (List.nodup_append.mp h').1

private theorem row_owned (L : HmrRowMulLayout) (A : Arena) (owned : L.data⊆A.live) :
    (L.row.sign::L.row.payload).toFinset⊆A.live := by
  intro q hq
  apply owned
  simp only [HmrRowMulLayout.data,List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
  tauto

/-- Derive both lift and fold encodings from the signed physical row. The
whole-program postcondition is consumed only through an explicit producer spec. -/
theorem hmrRowMul_consumer (L : HmrRowMulLayout) (H : RecordedProgram)
    (spec : HmrRowMulSpec L H) (A B : Arena)
    (owned : L.data⊆A.live) (borrow : A.borrowMany 24=some (B,L.anc))
    (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (ready : A.Ready s.basis) (legal : spec.legalCursor cursor) (pre : HmrRowMulPre L call s) :
    MagnitudeEncodes call.coefficient
      (fun q => s.basis (fusedPlacementMap (L.row.sign::L.row.payload++L.anc) q)) ∧
    regValue ((fusedFoldLow++fusedFoldHigh).map
      (fusedPlacementMap (fusedFoldPlacement L.row.payload L.out L.anc)))
      (run L.lift (tape.drop cursor) s).basis=call.coefficient.natAbs ∧
    regValue L.out (runWithTape H tape cursor s).basis=call.beforeSign ∧
    (runRecorded H ⟨tape,cursor⟩ s).2.cursor=cursor+recordedMeasurementCount H := by
  refine ⟨placedMagnitude_encoding L.row L.anc s.basis call.coefficient
    L.row_length pre.coefficient,?_,(spec.run call s tape cursor legal pre).1,rfl⟩
  exact placedSignedLift_fold_encoding A B L.row L.out L.anc L.row_length
    (row_distinct L) (row_owned L A owned) borrow call s (tape.drop cursor)
    ready pre.coefficient pre.lift_good

/-- Execute the journal first, derive C from the original signed row, and
then consume the abstract row-multiply certificate. No new scanWord premise. -/
theorem repacked_hmrRowMul_consumer (ms : List (Wire × Wire))
    (valid : ∀p∈ms,p.1≠p.2) (r : WindowRow)
    (L : HmrRowMulLayout) (row : L.row=repackedRow ms r)
    (H : RecordedProgram) (spec : HmrRowMulSpec L H) (A B : Arena)
    (owned : L.data⊆A.live) (borrow : A.borrowMany 24=some (B,L.anc))
    (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal : spec.legalCursor cursor)
    (coefficient : r.value s.basis=call.coefficient)
    (ready : A.Ready (run (repack ms) (tape.drop cursor) s).basis)
    (inputs : HmrRowMulInputs L call (run (repack ms) (tape.drop cursor) s)) :
    regValue L.out (runWithTape (embedRecorded (repack ms)++H) tape cursor s).basis=
      call.beforeSign := by
  have encoded : L.row.value (run (repack ms) (tape.drop cursor) s).basis=call.coefficient := by
    rw [row,repackedRow_value ms valid]
    exact coefficient
  have result := hmrRowMul_consumer L H spec A B owned borrow call
    (run (repack ms) (tape.drop cursor) s) tape cursor ready legal ⟨inputs,encoded⟩
  rw [runWithTape_append,runWithTape_embedRecorded]
  simpa only [(embedRecorded_counts _).2,repack_measurements,Nat.add_zero] using result.2.2.1

/-- The s2 source journal discharges journal validity; all producer obligations
remain explicit parameters. -/
theorem s2_hmrRowMul_consumer (r : WindowRow)
    (L : HmrRowMulLayout) (row : L.row=repackedRow s2SourceRepack r)
    (H : RecordedProgram) (spec : HmrRowMulSpec L H) (A B : Arena)
    (owned : L.data⊆A.live) (borrow : A.borrowMany 24=some (B,L.anc))
    (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal : spec.legalCursor cursor) (coefficient : r.value s.basis=call.coefficient)
    (ready : A.Ready (run (repack s2SourceRepack) (tape.drop cursor) s).basis)
    (inputs : HmrRowMulInputs L call (run (repack s2SourceRepack) (tape.drop cursor) s)) :
    regValue L.out (runWithTape (embedRecorded (repack s2SourceRepack)++H) tape cursor s).basis=
      call.beforeSign :=
  repacked_hmrRowMul_consumer s2SourceRepack
    (fun p hp => (s2SourceRepack_valid p hp).1) r L row H spec A B owned borrow
    call s tape cursor legal coefficient ready inputs

/-- The s6 source journal discharges journal validity; all producer obligations
remain explicit parameters. -/
theorem s6_hmrRowMul_consumer (r : WindowRow)
    (L : HmrRowMulLayout) (row : L.row=repackedRow s6SourceRepack r)
    (H : RecordedProgram) (spec : HmrRowMulSpec L H) (A B : Arena)
    (owned : L.data⊆A.live) (borrow : A.borrowMany 24=some (B,L.anc))
    (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal : spec.legalCursor cursor) (coefficient : r.value s.basis=call.coefficient)
    (ready : A.Ready (run (repack s6SourceRepack) (tape.drop cursor) s).basis)
    (inputs : HmrRowMulInputs L call (run (repack s6SourceRepack) (tape.drop cursor) s)) :
    regValue L.out (runWithTape (embedRecorded (repack s6SourceRepack)++H) tape cursor s).basis=
      call.beforeSign :=
  repacked_hmrRowMul_consumer s6SourceRepack
    (fun p hp => (s6SourceRepack_valid p hp).1) r L row H spec A B owned borrow
    call s tape cursor legal coefficient ready inputs

/-- s2 uses the actual state after HMR/corrections as the unpark input. Its
output word survives; the demolished multiplier, rather than out, is zero. -/
theorem s2_hmrUnpark_consumer (L : HmrRowMulLayout) (H K U : RecordedProgram)
    (spec : HmrRowUnparkSpec L U) (call : FusedCall) (original s : State)
    (tape : List Bool) (cursor : Nat)
    (input : spec.pre call original tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s)) :
    (∀q∈L.row.wires,(runWithTape (H++K++U) tape cursor s).basis q=original.basis q) ∧
    (∀q∈L.y,(runWithTape (H++K++U) tape cursor s).basis q=false) ∧
    (∀q∈L.out,(runWithTape (H++K++U) tape cursor s).basis q=
      (runWithTape (H++K) tape cursor s).basis q) ∧
    (runWithTape (H++K++U) tape cursor s).phase=
      xor (runWithTape (H++K) tape cursor s).phase
        (spec.phaseDebt tape (cursor+recordedMeasurementCount (H++K))
          (runWithTape (H++K) tape cursor s)) := by
  have h := spec.run call original _ tape _ input
  rw [runWithTape_append (H++K) U]
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2⟩

/-- s6 erase receives the intervening parked state, not an assumed immediate
forward result. Full signed row bits return and the owned output becomes zero. -/
theorem s6_hmrErase_consumer (L : HmrRowMulLayout) (H K R : RecordedProgram)
    (spec : HmrRowMulInvSpec L R) (call : FusedCall) (original s : State)
    (tape : List Bool) (cursor : Nat)
    (input : spec.pre call original tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s)) :
    (∀q∈L.row.wires,(runWithTape (H++K++R) tape cursor s).basis q=original.basis q) ∧
    (∀q∈L.out,(runWithTape (H++K++R) tape cursor s).basis q=false) ∧
    (runWithTape (H++K++R) tape cursor s).phase=
      xor (runWithTape (H++K) tape cursor s).phase
        (spec.phaseDebt tape (cursor+recordedMeasurementCount (H++K))
          (runWithTape (H++K) tape cursor s)) := by
  have h := spec.run call original _ tape _ input
  rw [runWithTape_append (H++K) R]
  exact ⟨h.1,h.2.2.1,h.2.2.2.2⟩

end ECDSAAdd.Arithmetic.Paper935
