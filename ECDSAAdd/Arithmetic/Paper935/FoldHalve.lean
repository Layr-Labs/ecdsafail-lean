import ECDSAAdd.Arithmetic.Paper935.FoldParity
import ECDSAAdd.Arithmetic.Paper935.FoldRotate
import ECDSAAdd.Arithmetic.Paper935.ScalingNoBorrow

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- The author's unconditional fold stage: copy the low bit, subtract the
windowed even literal, release the copy, then perform adjacent swaps. -/
def foldHalveProgram : Program := foldParityProgram++rotateRight fold256Word

private theorem word_nodup : fold256Word.Nodup := List.nodup_range'

private theorem word_outside (q : Wire) (outside : q=0 ∨ 257≤q) : q∉fold256Word := by
  intro mem
  simp only [fold256Word,List.mem_range'] at mem
  dsimp only [Wire] at *
  omega

/-- Unconditional circuit semantics, including the failing-window inputs:
the actual output is the truncated foldedHalf operation. -/
theorem foldHalve_contract (s : State) (m : List Bool)
    (ready : Fold256Ready s.basis) (zero : s.basis 0=false) :
    let out := run foldHalveProgram m s
    regValue fold256Word out.basis=foldedHalf 256 58 (2^32+977) (regValue fold256Word s.basis) ∧
    Fold256Ready out.basis ∧ out.basis 0=false ∧ out.phase=s.phase := by
  have prepared := foldParity_contract s m ready zero
  dsimp only at prepared
  generalize ht : run foldParityProgram m s=t at prepared
  let tape := m.drop (measurementCount foldParityProgram)
  have rotated := foldRotate_value fold256Word word_nodup t tape
  have frame := rotate_frame fold256Word t tape
  dsimp only [tape] at rotated frame
  dsimp only
  rw [foldHalveProgram,run_append,run_take,ht]
  refine ⟨?_,?_,?_,frame.1.trans prepared.2.2.2⟩
  · rw [rotated,prepared.1]
    simp only [foldedHalf,fold256Word,List.length_range']
    rfl
  · intro i hi
    rw [frame.2.1 (257+i) (word_outside _ (Or.inr (by dsimp only [Wire]; omega)))]
    exact prepared.2.1 i hi
  · exact (frame.2.1 0 (word_outside 0 (Or.inl rfl))).trans prepared.2.2.1

/-- On the shared explicit no-borrow event, this actual circuit implements
ideal secp256k1 halving. The event is not assumed to have any numeric mass. -/
theorem foldHalve_correct (s : State) (m : List Bool)
    (ready : Fold256Ready s.basis) (zero : s.basis 0=false)
    (good : FoldNoBorrow 58 (2^32+977) (regValue fold256Word s.basis)) :
    regValue fold256Word (run foldHalveProgram m s).basis=
      halveMod (2^256-(2^32+977)) (regValue fold256Word s.basis) := by
  rw [(foldHalve_contract s m ready zero).1]
  exact foldedHalf_correct 256 58 (2^32+977) _ (by decide) (by decide)
    (by decide) (by decide) (by decide) good

end ECDSAAdd.Arithmetic.Paper935
