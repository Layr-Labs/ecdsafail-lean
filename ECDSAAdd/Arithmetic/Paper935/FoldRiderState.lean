import ECDSAAdd.Arithmetic.Paper935.FoldRiderPhysical

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Inactive means full-state identity, not only equality of the word's
numeric value. This includes the arbitrary measurement phase and all outsiders. -/
theorem foldRider_inactive (s : State) (m : List Bool)
    (ready : Fold256Ready s.basis) (zero : s.basis 0=false) (inactive : s.basis 273=false) :
    run foldRiderProgram m s=s := by
  have contract := foldRider_contract s m ready zero
  dsimp only at contract
  generalize execution : run foldRiderProgram m s=out at contract ⊢
  rw [inactive] at contract
  simp only [Bool.false_eq_true,if_false] at contract
  have phase : out.phase=s.phase := contract.2.2.2.2
  have basis : out.basis=s.basis := by
    funext q
    by_cases atZero : q=0
    · subst q
      exact contract.2.2.1.trans zero.symm
    by_cases data : q<257
    · have member : q∈fold256Word := by
        simp only [fold256Word,List.mem_range']
        refine ⟨q-1,?_,?_⟩ <;> dsimp only [Wire] at * <;> omega
      exact (regValue_eq_iff fold256Word out.basis s.basis).mp contract.1 q member
    by_cases pool : q<273
    · have low : 257≤q := by
        dsimp only [Wire] at *
        omega
      have index : q=257+(q-257) := by dsimp only [Wire] at *; omega
      rw [index]
      exact (contract.2.1 (q-257) (by dsimp only [Wire] at *; omega)).trans
        (ready (q-257) (by dsimp only [Wire] at *; omega)).symm
    by_cases alive : q=273
    · subst q
      exact contract.2.2.2.1.trans inactive.symm
    · have outside : q∉Finset.range 274 := by
        simp only [Finset.mem_range]
        dsimp only [Wire] at *
        omega
      have original := run_preserves_outside foldRiderProgram m s q
        (Finset.notMem_mono foldRider_support outside)
      rw [execution] at original
      exact original

  cases out
  cases s
  exact congrArg₂ State.mk phase basis

end ECDSAAdd.Arithmetic.Paper935
