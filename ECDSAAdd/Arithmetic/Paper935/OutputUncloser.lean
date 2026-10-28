import ECDSAAdd.Arithmetic.Paper935.UncloserContract
import ECDSAAdd.Framework.OutputFrame

namespace ECDSAAdd.Arithmetic.Paper935

/-- Restore the uncloser boundary except for a declared output. Released
payloads and the gv sign must still be clean, and no phase debt is allowed. -/
structure OutputUncloserReady (O : Finset Wire) (b : WindowBank) (before reused : State) : Prop where
  phase : reused.phase=before.phase
  clean : ∀ q∈b.gv.sign::closerPayloads b,reused.basis q=false
  frame : ∀ q∉O,q∉b.gv.sign::closerPayloads b → reused.basis q=before.basis q

/-- The explicit bit conditions identify E's result as the real closer result
with only its declared output replaced. -/
theorem OutputUncloserReady.eq_withOutput (O : Finset Wire) (v : BasisState)
    (b : WindowBank) (p : Nat) (geometry : (b.rows.flatMap WindowRow.wires).Nodup)
    (fwidth : 1<2^b.f.payload.length) (positive : 0<p) (pwidth : p<2^b.gv.payload.length)
    (before reused : State) (m : List Bool) (gzero : b.g.value before.basis=0)
    (funit : (b.f.value before.basis).natAbs=1)
    (gvValue : b.gv.value before.basis=b.f.value before.basis*p)
    (restored : OutputUncloserReady O b before reused) (output : ∀ q∈O,reused.basis q=v q) :
    reused=withOutput O v (run (closerProgram b p) m before) := by
  have clear := closerProgram_clear b p geometry fwidth positive pwidth before m gzero funit gvValue
  dsimp only at clear
  generalize execution : run (closerProgram b p) m before=out at clear ⊢
  have phase : reused.phase=out.phase := restored.phase.trans clear.1.symm
  have basis : reused.basis=(withOutput O v out).basis := by
    funext q
    by_cases ho : q∈O
    · simpa only [withOutput,if_pos ho] using output q ho
    · simp only [withOutput,if_neg ho]
      by_cases hc : q∈b.gv.sign::closerPayloads b
      · rw [restored.clean q hc]
        rcases List.mem_cons.mp hc with eq | mem
        · subst q; exact clear.2.2.1.symm
        · exact (clear.2.1 q mem).symm
      · exact (restored.frame q ho hc).trans (clear.2.2.2 q hc).symm
  have phases : reused.phase=(withOutput O v out).phase := phase
  cases reused
  cases out
  exact congrArg₂ State.mk phases basis

end ECDSAAdd.Arithmetic.Paper935
