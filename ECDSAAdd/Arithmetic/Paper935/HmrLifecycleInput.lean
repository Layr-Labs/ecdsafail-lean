import ECDSAAdd.Arithmetic.Paper935.HmrLifecyclePhase

namespace ECDSAAdd.Arithmetic.Paper935

/-- Basis facts at a parked-row boundary. This does not assert phase cleanup. -/
structure HmrParkedBoundary (L : HmrRowMulLayout) (original : State)
    (tape : List Bool) (start : Nat) (current : State) : Prop where
  sign : current.basis L.row.sign=original.basis L.row.sign
  payload : ∀q∈L.row.payload,current.basis q=(L.parked tape start original).basis q
  scratch : ∀q∈L.scratch,current.basis q=false

structure HmrUnparkBoundary (L : HmrRowMulLayout) (original : State)
    (tape : List Bool) (start : Nat) (current : State) : Prop
    extends HmrParkedBoundary L original tape start current where
  demolished : ∀q∈L.y,current.basis q=false

structure HmrEraseBoundary (L : HmrRowMulLayout) (call : FusedCall) (original : State)
    (tape : List Bool) (start : Nat) (current : State) : Prop
    extends HmrParkedBoundary L original tape start current where
  multiplier : ∀q∈L.y,current.basis q=original.basis q
  output : regValue L.out current.basis=call.beforeSign

/-- The producer must prove that the original call precondition, concrete basis facts and record
conditions suffice for its predicate. No source instance is asserted. -/
structure HmrUnparkInputRule (L : HmrRowMulLayout) (U : RecordedProgram)
    (spec : HmrRowUnparkSpec L U) where
  records : List Bool → Nat → Nat → Prop
  accepts : ∀call original tape start cursor current,
    HmrRowMulPre L call original →
    records tape start cursor → HmrUnparkBoundary L original tape start current →
    spec.pre call original tape cursor current

structure HmrEraseInputRule (L : HmrRowMulLayout) (R : RecordedProgram)
    (spec : HmrRowMulInvSpec L R) where
  records : List Bool → Nat → Nat → Prop
  accepts : ∀call original tape start cursor current,
    HmrRowMulPre L call original →
    records tape start cursor → HmrEraseBoundary L call original tape start current →
    spec.pre call original tape cursor current

/-- Only a basis frame is needed: K may change phase, including by recorded
Z corrections. A support-disjointness proof is sufficient but not required. -/
theorem hmr_parked_boundary (L : HmrRowMulLayout) (H K : RecordedProgram)
    (forward : HmrRowMulSpec L H) (call : FusedCall) (s : State)
    (tape : List Bool) (cursor : Nat) (legal : forward.legalCursor cursor)
    (pre : HmrRowMulPre L call s)
    (frame : ∀q∈(L.row.sign::L.row.payload).toFinset∪L.scratch,
      (runWithTape (H++K) tape cursor s).basis q=(runWithTape H tape cursor s).basis q) :
    HmrParkedBoundary L s tape cursor (runWithTape (H++K) tape cursor s) := by
  have h := forward.run call s tape cursor legal pre
  constructor
  · rw [frame L.row.sign (by simp)]
    exact h.2.2.1
  · intro q hq
    rw [frame q (by simp [hq])]
    exact h.2.2.2.1 q hq
  · intro q hq
    rw [frame q (Finset.mem_union_right _ hq)]
    exact h.2.2.2.2.1 q hq

theorem hmr_unpark_input (L : HmrRowMulLayout) (H K U : RecordedProgram)
    (forward : HmrRowMulSpec L H) (unpark : HmrRowUnparkSpec L U)
    (rule : HmrUnparkInputRule L U unpark) (call : FusedCall) (s : State)
    (tape : List Bool) (cursor : Nat) (legal : forward.legalCursor cursor)
    (pre : HmrRowMulPre L call s)
    (frame : ∀q∈(L.row.sign::L.row.payload).toFinset∪L.scratch,
      (runWithTape (H++K) tape cursor s).basis q=(runWithTape H tape cursor s).basis q)
    (demolished : ∀q∈L.y,(runWithTape (H++K) tape cursor s).basis q=false)
    (records : rule.records tape cursor (cursor+recordedMeasurementCount (H++K))) :
    unpark.pre call s tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s) := by
  apply rule.accepts call s tape cursor _ _ pre records
  exact ⟨hmr_parked_boundary L H K forward call s tape cursor legal pre frame,demolished⟩

theorem hmr_erase_input (L : HmrRowMulLayout) (H K R : RecordedProgram)
    (forward : HmrRowMulSpec L H) (erase : HmrRowMulInvSpec L R)
    (rule : HmrEraseInputRule L R erase) (call : FusedCall) (s : State)
    (tape : List Bool) (cursor : Nat) (legal : forward.legalCursor cursor)
    (pre : HmrRowMulPre L call s)
    (frame : ∀q∈L.support,
      (runWithTape (H++K) tape cursor s).basis q=(runWithTape H tape cursor s).basis q)
    (records : rule.records tape cursor (cursor+recordedMeasurementCount (H++K))) :
    erase.pre call s tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s) := by
  have h := forward.run call s tape cursor legal pre
  apply rule.accepts call s tape cursor _ _ pre records
  constructor
  · apply hmr_parked_boundary L H K forward call s tape cursor legal pre
    intro q hq
    apply frame q
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons] at hq
    rcases hq with (rfl|hq)|hq
    · simp [HmrRowMulLayout.support,HmrRowMulLayout.data]
    · simp [HmrRowMulLayout.support,HmrRowMulLayout.data,hq]
    · exact Finset.mem_union_right _ hq
  · intro q hq
    rw [frame q (by simp [HmrRowMulLayout.support,HmrRowMulLayout.data,hq])]
    exact h.2.1 q hq
  · have eq : regValue L.out (runWithTape (H++K) tape cursor s).basis=
        regValue L.out (runWithTape H tape cursor s).basis := by
      apply regValue_congr
      intro q hq
      exact frame q (by simp [HmrRowMulLayout.support,HmrRowMulLayout.data,hq])
    exact eq.trans h.1

end ECDSAAdd.Arithmetic.Paper935
