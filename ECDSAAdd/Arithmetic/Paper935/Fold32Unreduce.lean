import ECDSAAdd.Arithmetic.Paper935.Fold32ReducePhysical

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Undo the bounded reduction while consuming its retained comparison flag. -/
def fold32Unreduce : Program :=
  fold32FlagProgram (Nat.testBit (2^257-fold32Prime)) ++
    [.CX 257 290] ++ fold32Program (Nat.testBit fold32Prime)

private theorem restore_math (y : Nat) (b : Bool) (hy : y<fold32Prime) :
    ((y+(if b then 2^257-fold32Prime else 0))%2^257+fold32Prime)%2^257=
      y+(if b then 0 else fold32Prime) := by
  cases b <;> norm_num [fold32Prime] at * <;> omega

private theorem high_math (y : Nat) (b : Bool) (hy : y<fold32Prime) :
    (2^256≤(y+(if b then 2^257-fold32Prime else 0))%2^257) ↔ b=true := by
  cases b <;> norm_num [fold32Prime] at * <;> omega

private theorem high_iff (s : BasisState) : s 257=true ↔ 2^256≤regValue fold32Word s := by
  have split : fold32Word=List.range' 1 256++[257] := by decide +kernel
  rw [split]
  simpa only [List.length_range'] using regValue_highBit (List.range' 1 256) 257 s

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

/-- A canonical remainder and either comparison flag reconstruct the bounded
word. The comparison flag and shared pool are physically cleared. -/
theorem fold32Unreduce_contract (s : State) (m : List Bool)
    (ready : Fold32Ready 0 s.basis) (enabled : s.basis 0=true)
    (bound : regValue fold32Word s.basis<fold32Prime) :
    let out := run fold32Unreduce m s
    regValue fold32Word out.basis=regValue fold32Word s.basis+
      (if s.basis 290 then 0 else fold32Prime) ∧
    Fold32Ready 0 out.basis ∧ out.basis 290=false ∧ out.basis 0=true ∧ out.phase=s.phase := by
  let first := fold32FlagProgram (Nat.testBit (2^257-fold32Prime))
  let a := run first m s
  let tape := m.drop (measurementCount first)
  let b := run [.CX 257 290] tape a
  have ha := fold32FlagProgram_contract (Nat.testBit (2^257-fold32Prime)) s m ready
  dsimp only at ha
  rw [fold32_literal_negative_prime] at ha
  have control : a.basis 0=true := (fold32FlagProgram_control _ s m).trans enabled
  have high : a.basis 257=s.basis 290 := by
    apply Bool.eq_iff_iff.mpr
    rw [high_iff,ha.1]
    exact high_math _ _ bound
  have fa : a.basis 290=s.basis 290 := ha.2.2.1
  have fb : b.basis 290=false := by
    simp only [b,run,writeBit,Function.update_self,high,fa,Bool.xor_self]
  have cb : b.basis 0=true := by
    simpa only [b,run,writeBit,Function.update_of_ne (show (0 : Wire)≠290 by decide)] using control
  have wb := capture_word a tape
  have rb := capture_ready a tape ha.2.1
  have hc := fold32Program_contract (Nat.testBit fold32Prime) b tape rb
  dsimp only at hc
  rw [fold32_literal_prime,cb,if_pos rfl,wb,ha.1] at hc
  have flagOut : (run (fold32Program (Nat.testBit fold32Prime)) tape b).basis 290=false := by
    rw [run_preserves_outside _ _ _ 290 ?_]
    · exact fb
    · intro h
      have := Finset.mem_range.mp (fold32Program_support (Nat.testBit fold32Prime) h)
      omega
  have output : run fold32Unreduce m s=run (fold32Program (Nat.testBit fold32Prime)) tape b := by
    simp only [fold32Unreduce,run_append,run_take,measurementCount_append,measurementCount,Nat.add_zero]
    rfl
  rw [output]
  exact ⟨hc.1.trans (restore_math _ _ bound),hc.2.1,flagOut,hc.2.2.1,hc.2.2.2.trans ha.2.2.2⟩

end ECDSAAdd.Arithmetic.Paper935
