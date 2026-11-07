import ECDSAAdd.Submission.Entrant.Fast08
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.ZeroFill
open Arithmetic

def finishUOne (a : Nat) (one U : Wire) (low : List (Nat × Wire × Wire)) : Program :=
  xorAcc a U low ++ [.X one]

theorem finishUOne_correct (a : Nat) (one U : Wire) (low : List (Nat × Wire × Wire))
    (hone : one ≠ U) (hLow : ∀ x ∈ low, x.2.1 ≠ U ∧ x.2.2 ≠ U)
    (s : State) (m : List Bool) (hU : s.basis U = accVal a s.basis low) :
    run (finishUOne a one U low) m s =
      ⟨s.phase, writeBit (writeBit s.basis U false) one (!s.basis one)⟩ := by
  unfold finishUOne
  rw [run_cat _ _ (xorAcc_mc a U low), run_xorAcc a U low hLow]
  simp [xw, run, hU, writeBit, Function.update_of_ne hone]

theorem finishUOne_counts (a : Nat) (one U : Wire) (low : List (Nat × Wire × Wire)) :
    toffoliCount (finishUOne a one U low) = 0 ∧ measurementCount (finishUOne a one U low) = 0 := by
  simp [finishUOne, toffoliCount_append, measurementCount_append, xorAcc_tc, xorAcc_mc, toffoliCount, measurementCount]
end ECDSAAdd.Entrant.ZeroFill
