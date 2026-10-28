import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetHead

set_option maxRecDepth 4096
set_option maxHeartbeats 500000
namespace ECDSAAdd.Arithmetic.TerminalParityMeasure

def program (a b cin target : Wire) : Program :=
  [.X target]++eraseCarry a b cin target

/-- The input flag already holds the complemented majority. Measure that
flag directly; each fresh outcome receives its actual quadratic correction. -/
theorem correct (a b cin target : Wire)
    (ha : a≠target) (hb : b≠target) (hc : cin≠target)
    (s : State) (m : List Bool)
    (ht : s.basis target= !(carryBit (s.basis a) (s.basis b) (s.basis cin))) :
    run (program a b cin target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
  let u := run [.X target] [] s
  have hu : u=⟨s.phase,writeBit s.basis target (!s.basis target)⟩ := rfl
  have hcarry : u.basis target=carryBit (u.basis a) (u.basis b) (u.basis cin) := by
    simp only [hu,writeBit,Function.update_self,Function.update_of_ne ha,
      Function.update_of_ne hb,Function.update_of_ne hc,ht,Bool.not_not]
  rw [program,run_append]
  simp only [show measurementCount [.X target]=0 from rfl,List.take_zero,List.drop_zero]
  change run (eraseCarry a b cin target) m u=_
  rw [eraseCarry_correct a b cin target ha hb hc u hcarry m,hu]
  apply State.extensionality
  · rfl
  · funext q
    by_cases hq : q=target
    · subst q
      simp [writeBit]
    · simp [writeBit,hq]

theorem counts (a b cin target : Wire) :
    toffoliCount (program a b cin target)=0 ∧
    measurementCount (program a b cin target)=1 := by
  simp [program,eraseCarry,toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.TerminalParityMeasure
#print axioms ECDSAAdd.Arithmetic.TerminalParityMeasure.correct
#print axioms ECDSAAdd.Arithmetic.TerminalParityMeasure.counts
