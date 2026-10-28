import ECDSAAdd.Arithmetic.Paper935.CloserRelease

namespace ECDSAAdd.Arithmetic.Paper935

/-- A caller may reuse the released payloads, but must return them clean before
unclosing. The gv sign remains owned and must also retain its cleared value.
All other bits and the phase must match the pre-closer state for full recovery. -/
structure UncloserReady (b : WindowBank) (before reused : State) : Prop where
  phase : reused.phase=before.phase
  clean : ∀ q∈b.gv.sign::closerPayloads b,reused.basis q=false
  frame : ∀ q∉b.gv.sign::closerPayloads b,reused.basis q=before.basis q

/-- The caller-facing restoration conditions reconstruct the physical closer
output; they do not assume an equality with an interpreter execution. -/
theorem UncloserReady.eq_closer (b : WindowBank) (p : Nat)
    (geometry : (b.rows.flatMap WindowRow.wires).Nodup)
    (fwidth : 1<2^b.f.payload.length) (positive : 0<p)
    (pwidth : p<2^b.gv.payload.length) (before reused : State) (m : List Bool)
    (gzero : b.g.value before.basis=0) (funit : (b.f.value before.basis).natAbs=1)
    (gvValue : b.gv.value before.basis=b.f.value before.basis*p)
    (restored : UncloserReady b before reused) :
    reused=run (closerProgram b p) m before := by
  have clear := closerProgram_clear b p geometry fwidth positive pwidth before m gzero funit gvValue
  dsimp only at clear
  generalize execution : run (closerProgram b p) m before=out at clear ⊢
  have phase : reused.phase=out.phase := restored.phase.trans clear.1.symm
  have basis : reused.basis=out.basis := by
    funext q
    by_cases h : q∈b.gv.sign::closerPayloads b
    · rw [restored.clean q h]
      rcases List.mem_cons.mp h with eq | mem
      · subst q; exact clear.2.2.1.symm
      · exact (clear.2.1 q mem).symm
    · exact (restored.frame q h).trans (clear.2.2.2 q h).symm
  cases reused
  cases out
  exact congrArg₂ State.mk phase basis

/-- Once the caller discharges the explicit bit and phase restoration
conditions, the uncloser restores the entire original state for any tape. -/
theorem closerProgram_unclose (b : WindowBank) (p : Nat)
    (geometry : (b.rows.flatMap WindowRow.wires).Nodup)
    (fwidth : 1<2^b.f.payload.length) (positive : 0<p)
    (pwidth : p<2^b.gv.payload.length) (before reused : State) (n : List Bool)
    (gzero : b.g.value before.basis=0) (funit : (b.f.value before.basis).natAbs=1)
    (gvValue : b.gv.value before.basis=b.f.value before.basis*p)
    (restored : UncloserReady b before reused) :
    run (closerProgram b p).reverse n reused=before := by
  rw [restored.eq_closer b p geometry fwidth positive pwidth before reused [] gzero funit gvValue]
  exact closerProgram_roundtrip b p geometry before [] n

/-- Reclaiming exactly the released payload set restores the old ownership;
no still-live sign, coefficient, or history site is borrowed. -/
theorem closer_reclaim (b : WindowBank) (A : Arena) (owned : rowsOwned A b.rows) :
    (A.retireSet (closerPayloads b).toFinset).reserve (closerPayloads b).toFinset=some A := by
  have sub : (closerPayloads b).toFinset⊆A.live := by
    intro q hq
    apply owned.2
    simp only [List.mem_toFinset,closerPayloads,List.mem_append] at hq
    simp only [List.mem_toFinset,WindowBank.rows,List.flatMap_cons,List.flatMap_nil,
      WindowRow.wires,List.mem_append,List.mem_cons,List.not_mem_nil]
    tauto
  have apart : Disjoint (A.live\(closerPayloads b).toFinset) (closerPayloads b).toFinset :=
    Finset.disjoint_left.mpr (fun _ hq h => (Finset.mem_sdiff.mp hq).2 h)
  unfold Arena.reserve Arena.retireSet
  rw [dif_pos ⟨sub.trans A.bounded,apart⟩]
  congr 1
  have sets : A.live\(closerPayloads b).toFinset ∪ (closerPayloads b).toFinset=A.live := by
    ext q
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact sub h
    · intro h
      by_cases mem : q∈(closerPayloads b).toFinset
      · exact Or.inr mem
      · exact Or.inl ⟨h,mem⟩
  cases A
  congr 1

/-- The complete uncloser boundary: restored bits imply the retired arena is
Ready, reservation recovers ownership, and inverse execution restores both
full state and the original Ready invariant. -/
theorem closerProgram_reclaim_unclose (b : WindowBank) (p : Nat) (A : Arena)
    (owned : rowsOwned A b.rows) (fwidth : 1<2^b.f.payload.length)
    (positive : 0<p) (pwidth : p<2^b.gv.payload.length) (before reused : State) (n : List Bool)
    (ready : A.Ready before.basis) (gzero : b.g.value before.basis=0)
    (funit : (b.f.value before.basis).natAbs=1)
    (gvValue : b.gv.value before.basis=b.f.value before.basis*p)
    (restored : UncloserReady b before reused) :
    (A.retireSet (closerPayloads b).toFinset).Ready reused.basis ∧
    (A.retireSet (closerPayloads b).toFinset).reserve (closerPayloads b).toFinset=some A ∧
    run (closerProgram b p).reverse n reused=before ∧
    A.Ready (run (closerProgram b p).reverse n reused).basis := by
  have inverse := closerProgram_unclose b p owned.1 fwidth positive pwidth before reused n
    gzero funit gvValue restored
  refine ⟨?_,closer_reclaim b A owned,inverse,by rw [inverse]; exact ready⟩
  rw [restored.eq_closer b p owned.1 fwidth positive pwidth before reused [] gzero funit gvValue]
  exact (closerProgram_release b p A owned fwidth positive pwidth before [] ready gzero funit gvValue).2

end ECDSAAdd.Arithmetic.Paper935
