import ECDSAAdd.Arithmetic.Paper935.Fold32Control

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Subtract p, retain the underflow flag, then restore p exactly when needed.
Control 0 must be true; comparison flag 290 must be zero. -/
def fold32Reduce : Program :=
  fold32Program (Nat.testBit (2^257-fold32Prime)) ++
    [.CX 257 290] ++ fold32FlagProgram (Nat.testBit fold32Prime)

private theorem high_iff (s : BasisState) :
    s 257=true ↔ 2^256≤regValue fold32Word s := by
  have split : fold32Word=List.range' 1 256++[257] := by decide +kernel
  rw [split]
  simpa only [List.length_range'] using regValue_highBit (List.range' 1 256) 257 s

private theorem underflow (x : Nat) (hx : x<2*fold32Prime) :
    2^256≤(x+(2^257-fold32Prime))%2^257 ↔ x<fold32Prime := by
  norm_num [fold32Prime] at *
  omega

private theorem capture_word (s : State) (m : List Bool) :
    regValue fold32Word (run [.CX 257 290] m s).basis=regValue fold32Word s.basis := by
  apply regValue_congr
  intro q hq
  have away : q≠290 := by
    simp only [fold32Word,List.mem_range'] at hq
    dsimp only [Wire] at *
    omega
  simp only [run,writeBit,Function.update_of_ne away]

private theorem capture_ready (s : State) (m : List Bool) (h : Fold32Ready 0 s.basis) :
    Fold32Ready 0 (run [.CX 257 290] m s).basis := by
  intro i hi lower
  have away : (258+i : Wire)≠290 := by dsimp only [Wire]; omega
  simpa only [run,writeBit,Function.update_of_ne away] using h i hi lower

attribute [local irreducible] fold32Program fold32FlagProgram

/-- Canonical result with an explicit retained comparison bit. The latter
records x<p; it is not silently discarded by a non-injective reduction. -/
theorem fold32Reduce_contract (s : State) (m : List Bool)
    (ready : Fold32Ready 0 s.basis) (enabled : s.basis 0=true)
    (flag : s.basis 290=false) (bound : regValue fold32Word s.basis<2*fold32Prime) :
    let out := run fold32Reduce m s
    regValue fold32Word out.basis=regValue fold32Word s.basis%fold32Prime ∧
    Fold32Ready 0 out.basis ∧
    out.basis 290=decide (regValue fold32Word s.basis<fold32Prime) ∧ out.phase=s.phase := by
  let first := fold32Program (Nat.testBit (2^257-fold32Prime))
  let a := run first m s
  let tape := m.drop (measurementCount first)
  let b := run [.CX 257 290] tape a
  have ha := fold32Program_contract (Nat.testBit (2^257-fold32Prime)) s m ready
  dsimp only at ha
  rw [fold32_literal_negative_prime,enabled,if_pos rfl] at ha
  have fa : a.basis 290=false := by
    change (run first m s).basis 290=false
    rw [run_preserves_outside first m s 290 ?_]
    · exact flag
    · intro h
      have := Finset.mem_range.mp (fold32Program_support (Nat.testBit (2^257-fold32Prime)) h)
      omega
  have high : a.basis 257=decide (regValue fold32Word s.basis<fold32Prime) := by
    apply Bool.eq_iff_iff.mpr
    rw [high_iff,ha.1]
    simpa only [decide_eq_true_eq] using underflow (regValue fold32Word s.basis) bound
  have fb : b.basis 290=decide (regValue fold32Word s.basis<fold32Prime) := by
    simp only [b,run,writeBit,Function.update_self,fa,Bool.false_xor,high]
  have wb := capture_word a tape
  have rb := capture_ready a tape ha.2.1
  have hc := fold32FlagProgram_contract (Nat.testBit fold32Prime) b tape rb
  dsimp only at hc
  rw [fold32_literal_prime,fb,wb,ha.1] at hc
  have numeric := fold32_reduce_math (regValue fold32Word s.basis) bound
  have output : run fold32Reduce m s=run (fold32FlagProgram (Nat.testBit fold32Prime)) tape b := by
    simp only [fold32Reduce,run_append,run_take,measurementCount_append,measurementCount,Nat.add_zero]
    rfl
  rw [output]
  refine ⟨hc.1.trans ?_,hc.2.1,hc.2.2.1,?_⟩
  · simpa only [decide_eq_true_eq] using numeric
  · exact hc.2.2.2.trans ha.2.2.2

end ECDSAAdd.Arithmetic.Paper935
