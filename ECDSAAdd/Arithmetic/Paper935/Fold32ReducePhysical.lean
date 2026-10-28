import ECDSAAdd.Arithmetic.Paper935.Fold32Reduce

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic RecordedQuantum

attribute [local irreducible] fold32Program fold32FlagProgram

theorem fold32Reduce_physical : GatePhysical fold32Reduce := by
  rw [fold32Reduce,gatePhysical_append,gatePhysical_append]
  exact ⟨⟨fold32Program_physical _,by simp [GatePhysical,PhysicalInstr,ProperGate]⟩,
    fold32FlagProgram_physical _⟩

theorem fold32Reduce_support : wires fold32Reduce⊆Finset.range 291 := by
  rw [fold32Reduce,wires_append,wires_append,Finset.union_subset_iff,Finset.union_subset_iff]
  refine ⟨⟨?_,?_⟩,fold32FlagProgram_support _⟩
  · intro q h
    exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp (fold32Program_support _ h)) (by decide))
  · simp [wires,Instr.wires,Finset.subset_iff]

theorem fold32Reduce_frame (s : State) (m : List Bool) (q : Wire) (hq : 291≤q) :
    (run fold32Reduce m s).basis q=s.basis q := by
  apply run_preserves_outside
  intro h
  have := Finset.mem_range.mp (fold32Reduce_support h)
  dsimp only [Wire] at *
  omega

theorem fold32Reduce_control (s : State) (m : List Bool) (ready : Fold32Ready 0 s.basis) :
    (run fold32Reduce m s).basis 0=s.basis 0 := by
  rw [fold32Reduce,run_append,run_take,fold32FlagProgram_control,run_append,run_take]
  simp only [run,writeBit,Function.update_of_ne (show (0 : Wire)≠290 by decide)]
  exact (fold32Program_contract _ s m ready).2.2.1

/-- The retained comparison flag reconstructs the original bounded word;
this is an information-preservation theorem, not an inverse gate program. -/
theorem fold32Reduce_reconstruct (s : State) (m : List Bool)
    (ready : Fold32Ready 0 s.basis) (enabled : s.basis 0=true)
    (flag : s.basis 290=false) (bound : regValue fold32Word s.basis<2*fold32Prime) :
    let out := run fold32Reduce m s
    regValue fold32Word s.basis=regValue fold32Word out.basis+
      (if out.basis 290 then 0 else fold32Prime) := by
  have h := fold32Reduce_contract s m ready enabled flag bound
  dsimp only at h ⊢
  rw [h.1,h.2.2.1]
  simp only [decide_eq_true_eq]
  norm_num [fold32Prime] at bound ⊢
  split_ifs <;> omega

/-- The high data bit is zero after canonical reduction. -/
theorem fold32Reduce_high_zero (s : State) (m : List Bool)
    (ready : Fold32Ready 0 s.basis) (enabled : s.basis 0=true)
    (flag : s.basis 290=false) (bound : regValue fold32Word s.basis<2*fold32Prime) :
    (run fold32Reduce m s).basis 257=false := by
  have h := (fold32Reduce_contract s m ready enabled flag bound).1
  have limit : regValue fold32Word (run fold32Reduce m s).basis<2^256 := by
    rw [h]
    exact lt_trans (Nat.mod_lt _ (by norm_num [fold32Prime])) (by norm_num [fold32Prime])
  have split : fold32Word=List.range' 1 256++[257] := by decide +kernel
  have high := regValue_highBit (List.range' 1 256) 257 (run fold32Reduce m s).basis
  rw [←split] at high
  simp only [List.length_range'] at high
  cases hb : (run fold32Reduce m s).basis 257
  · rfl
  · have := high.mp hb
    omega

end ECDSAAdd.Arithmetic.Paper935
