import ECDSAAdd.Arithmetic.Paper935.Fold32Unreduce

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic RecordedQuantum

attribute [local irreducible] fold32Program fold32FlagProgram fold32Reduce fold32Unreduce

theorem fold32Unreduce_physical : GatePhysical fold32Unreduce := by
  rw [fold32Unreduce,gatePhysical_append,gatePhysical_append]
  exact ⟨⟨fold32FlagProgram_physical _,by simp [GatePhysical,PhysicalInstr,ProperGate]⟩,
    fold32Program_physical _⟩

theorem fold32Unreduce_support : wires fold32Unreduce⊆Finset.range 291 := by
  rw [fold32Unreduce,wires_append,wires_append,Finset.union_subset_iff,Finset.union_subset_iff]
  refine ⟨⟨fold32FlagProgram_support _,?_⟩,?_⟩
  · simp [wires,Instr.wires,Finset.subset_iff]
  · intro q h
    exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp (fold32Program_support _ h)) (by decide))

theorem fold32Unreduce_frame (s : State) (m : List Bool) (q : Wire) (hq : 291≤q) :
    (run fold32Unreduce m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro h
  have := Finset.mem_range.mp (fold32Unreduce_support h)
  dsimp only [Wire] at *
  omega

/-- Reduction followed by the actual restoration program returns the whole
basis state and phase for arbitrary, independently chosen measurement tapes. -/
theorem fold32Reduce_roundtrip (s : State) (m n : List Bool)
    (ready : Fold32Ready 0 s.basis) (enabled : s.basis 0=true)
    (flag : s.basis 290=false) (bound : regValue fold32Word s.basis<2*fold32Prime) :
    run fold32Unreduce n (run fold32Reduce m s)=s := by
  let t := run fold32Reduce m s
  have forward := fold32Reduce_contract s m ready enabled flag bound
  have control : t.basis 0=true := (fold32Reduce_control s m ready).trans enabled
  have canonical : regValue fold32Word t.basis<fold32Prime := by
    rw [forward.1]
    exact Nat.mod_lt _ (by norm_num [fold32Prime])
  have backward := fold32Unreduce_contract t n forward.2.1 control canonical
  have reconstruct := fold32Reduce_reconstruct s m ready enabled flag bound
  have word : regValue fold32Word (run fold32Unreduce n t).basis=regValue fold32Word s.basis :=
    backward.1.trans reconstruct.symm
  apply State.extensionality
  · exact backward.2.2.2.2.trans forward.2.2.2
  · funext q
    by_cases zero : q=0
    · subst q
      exact backward.2.2.2.1.trans enabled.symm
    by_cases data : q<258
    · apply (regValue_eq_iff fold32Word _ _).mp word q
      simp only [fold32Word,List.mem_range']
      refine ⟨q-1,?_,?_⟩ <;> dsimp only [Wire] at * <;> omega
    by_cases pool : q<290
    · have index : q=258+(q-258) := by dsimp only [Wire] at *; omega
      have upper : q-258<32 := by dsimp only [Wire] at *; omega
      rw [index]
      exact (backward.2.1 (q-258) upper (by omega)).trans (ready (q-258) upper (by omega)).symm
    by_cases isflag : q=290
    · subst q
      exact backward.2.2.1.trans flag.symm
    · have beyond : 291≤q := by dsimp only [Wire] at *; omega
      exact (fold32Unreduce_frame t n q beyond).trans (fold32Reduce_frame s m q beyond)

/-- The single concatenated program restores its input, including phase. -/
theorem fold32Reduce_append_unreduce (s : State) (m : List Bool)
    (ready : Fold32Ready 0 s.basis) (enabled : s.basis 0=true)
    (flag : s.basis 290=false) (bound : regValue fold32Word s.basis<2*fold32Prime) :
    run (fold32Reduce++fold32Unreduce) m s=s := by
  rw [run_append,run_take]
  exact fold32Reduce_roundtrip s m _ ready enabled flag bound

end ECDSAAdd.Arithmetic.Paper935
