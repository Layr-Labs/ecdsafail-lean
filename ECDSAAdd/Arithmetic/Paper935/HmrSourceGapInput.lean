import ECDSAAdd.Arithmetic.Paper935.HmrSignLifecycle

namespace ECDSAAdd.Arithmetic.Paper935
attribute [local irreducible] s2SourceGap s6SourceGap s2HmrSourceRow s6HmrSourceRow
  s2HmrSeamPorts s6HmrSeamPorts

/-- Actual K2 supplies the complete unpark basis boundary from the forward
certificate, including zero anc and flags. No phase conclusion is assumed. -/
theorem s2SourceGap_unpark_boundary (H : RecordedProgram)
    (forward : HmrRowMulSpec s2HmrSourceLayout H) (call : FusedCall) (s : State)
    (tape : List Bool) (cursor : Nat) (legal : forward.legalCursor cursor)
    (pre : HmrRowMulPre s2HmrSourceLayout call s) :
    HmrUnparkBoundary s2HmrSourceLayout s tape cursor
      (runWithTape (H++s2SourceGap) tape cursor s) := by
  have h := forward.run call s tape cursor legal pre
  have clean : ∀q∈s2HmrSeamPorts.anc,(runWithTape H tape cursor s).basis q=false := by
    intro q hq
    exact h.2.2.2.2.1 q (Finset.mem_union_left _ (List.mem_toFinset.mpr hq))
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · rw [runWithTape_append,s2SourceGap_row_frame tape _ _ _ (by change s2HmrSourceRow.sign∈s2HmrSourceRow.wires; simp [WindowRow.wires])]
    exact h.2.2.1
  · intro q hq
    rw [runWithTape_append,s2SourceGap_row_frame tape _ _ q (by change q∈s2HmrSourceRow.payload at hq; simp [WindowRow.wires,hq])]
    exact h.2.2.2.1 q hq
  · intro q hq
    rw [runWithTape_append]
    rcases Finset.mem_union.mp hq with anc | flag
    · exact s2SourceGap_anc _ tape _ clean q (List.mem_toFinset.mp anc)
    · rw [s2SourceGap_flags_frame tape _ _ q flag]
      exact h.2.2.2.2.1 q (Finset.mem_union_right _ flag)
  · rw [runWithTape_append]
    exact s2SourceGap_demolished tape _ _

/-- Only the producer's record predicate and acceptance rule remain; the
actual K2 basis-frame and demolition premises have been proved above. -/
theorem s2SourceGap_unpark_input (H U : RecordedProgram)
    (forward : HmrRowMulSpec s2HmrSourceLayout H)
    (unpark : HmrRowUnparkSpec s2HmrSourceLayout U)
    (rule : HmrUnparkInputRule s2HmrSourceLayout U unpark)
    (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal : forward.legalCursor cursor) (pre : HmrRowMulPre s2HmrSourceLayout call s)
    (records : rule.records tape cursor (cursor+recordedMeasurementCount (H++s2SourceGap))) :
    unpark.pre call s tape (cursor+recordedMeasurementCount (H++s2SourceGap))
      (runWithTape (H++s2SourceGap) tape cursor s) := by
  exact rule.accepts call s tape cursor _ _ pre records
    (s2SourceGap_unpark_boundary H forward call s tape cursor legal pre)

/-- Actual K6 restores all basis bits, so the inverse input relation needs
no additional caller-supplied support/frame assumption. -/
theorem s6SourceGap_erase_input (H R : RecordedProgram)
    (forward : HmrRowMulSpec s6HmrSourceLayout H)
    (erase : HmrRowMulInvSpec s6HmrSourceLayout R)
    (rule : HmrEraseInputRule s6HmrSourceLayout R erase)
    (call : FusedCall) (s : State) (tape : List Bool) (cursor : Nat)
    (legal : forward.legalCursor cursor) (pre : HmrRowMulPre s6HmrSourceLayout call s)
    (records : rule.records tape cursor (cursor+recordedMeasurementCount (H++s6SourceGap))) :
    erase.pre call s tape (cursor+recordedMeasurementCount (H++s6SourceGap))
      (runWithTape (H++s6SourceGap) tape cursor s) := by
  have h := forward.run call s tape cursor legal pre
  have clean : ∀q∈s6HmrSeamPorts.anc,(runWithTape H tape cursor s).basis q=false := by
    intro q hq
    exact h.2.2.2.2.1 q (Finset.mem_union_left _ (List.mem_toFinset.mpr hq))
  apply hmr_erase_input _ H s6SourceGap R forward erase rule call s tape cursor legal pre
  · intro q _
    rw [runWithTape_append,s6SourceGap_basis_of_anc _ tape _ clean]
  · exact records

end ECDSAAdd.Arithmetic.Paper935
