import ECDSAAdd.Arithmetic.Paper935.FoldRiderParity
import ECDSAAdd.Arithmetic.Paper935.ScalingNoBorrow
import ECDSAAdd.Arithmetic.Shift

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- The source's alive-controlled fold and Fredkin rotation. -/
def foldRiderProgram : Program := foldRiderParityProgram++shiftRight 273 fold256Word

private theorem shift_value (c : Wire) (r : List Wire) (hn : (c::r).Nodup) (s : State) (m : List Bool) :
    regValue r (run (shiftRight c r) m s).basis=
      if s.basis c then regValue r s.basis/2+(regValue r s.basis%2)*2^(r.length-1)
      else regValue r s.basis := by
  cases r with
  | nil => cases s.basis c <;> simp [regValue,shiftRight,run]
  | cons a bs =>
    rw [shiftRight_value c a bs hn s m]
    have value : regValue (a::bs) s.basis=(s.basis a).toNat+2*regValue bs s.basis := by
      simp only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite]
    rw [value]
    simp only [List.length_cons,Nat.add_sub_cancel]
    cases s.basis c <;> cases s.basis a <;> simp [Nat.mul_comm]
    omega

private theorem word_outside (q : Wire) (outside : q=0 ∨ 257≤q) : q∉fold256Word := by
  intro mem
  simp only [fold256Word,List.mem_range'] at mem
  dsimp only [Wire] at *
  omega

private theorem controlled_word_nodup : (273::fold256Word).Nodup :=
  List.nodup_cons.mpr ⟨word_outside _ (Or.inr (by decide)),List.nodup_range'⟩

/-- Actual controlled circuit, including the low-window failure branches.
The initial alive bit selects whether foldedHalf is performed. -/
theorem foldRider_contract (s : State) (m : List Bool)
    (ready : Fold256Ready s.basis) (zero : s.basis 0=false) :
    let out := run foldRiderProgram m s
    regValue fold256Word out.basis=
      (if s.basis 273 then foldedHalf 256 58 (2^32+977) (regValue fold256Word s.basis)
        else regValue fold256Word s.basis) ∧
    Fold256Ready out.basis ∧ out.basis 0=false ∧ out.basis 273=s.basis 273 ∧ out.phase=s.phase := by
  have prepared := foldRiderParity_contract s m ready zero
  dsimp only at prepared
  generalize ht : run foldRiderParityProgram m s=t at prepared
  let tape := m.drop (measurementCount foldRiderParityProgram)
  have rotated := shift_value 273 fold256Word controlled_word_nodup t tape
  have frame := shift_frame 273 fold256Word t tape
  dsimp only [tape] at rotated frame
  dsimp only
  rw [foldRiderProgram,run_append,run_take,ht]
  refine ⟨?_,?_,?_,?_,frame.1.trans prepared.2.2.2.2⟩
  · rw [rotated,prepared.1,prepared.2.2.2.1]
    cases s.basis 273 <;> simp only [Bool.false_eq_true,if_false,Bool.false_and,if_true,Bool.true_and,decide_eq_true_eq,
      foldedHalf,fold256Word,List.length_range']
    rfl
  · intro i hi
    rw [frame.2.1 (257+i) (word_outside _ (Or.inr (by dsimp only [Wire]; omega)))]
    exact prepared.2.1 i hi
  · exact (frame.2.1 0 (word_outside 0 (Or.inl rfl))).trans prepared.2.2.1
  · exact (frame.2.1 273 (word_outside 273 (Or.inr (by decide)))).trans prepared.2.2.2.1

/-- The actual alive-controlled rider implements ideal controlled halving
on the same explicit per-call event as the unconditional seam. -/
theorem foldRider_correct (s : State) (m : List Bool)
    (ready : Fold256Ready s.basis) (zero : s.basis 0=false)
    (good : s.basis 273=true → FoldNoBorrow 58 (2^32+977) (regValue fold256Word s.basis)) :
    regValue fold256Word (run foldRiderProgram m s).basis=
      if s.basis 273 then halveMod (2^256-(2^32+977)) (regValue fold256Word s.basis)
      else regValue fold256Word s.basis := by
  rw [(foldRider_contract s m ready zero).1]
  cases h : s.basis 273 with
  | false => simp only [Bool.false_eq_true,if_false]
  | true =>
    simp only [if_true]
    exact foldedHalf_correct 256 58 (2^32+977) _ (by decide) (by decide)
      (by decide) (by decide) (by decide) (good h)

end ECDSAAdd.Arithmetic.Paper935
