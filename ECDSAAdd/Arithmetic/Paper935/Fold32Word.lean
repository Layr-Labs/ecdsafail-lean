import ECDSAAdd.Arithmetic.Paper935.Fold32Value

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def fold32Prefix (bits : Nat → Bool) (n : Nat) (m : List Bool) (s : State) : State :=
  run ((List.range n).flatMap (fold32Forward bits)) m s

def fold32PartialLiteral (bits : Nat → Bool) (n : Nat) (enabled : Bool) : Nat :=
  ((List.range n).map fun j => 2^(fold32Starts[j]?.getD 0)*
    foldBlockLiteral (fold32Cells bits j false) enabled).sum

private theorem prefix_succ (bits : Nat → Bool) (n : Nat) (m : List Bool) (s : State) :
    fold32Prefix bits (n+1) m s=run (fold32Forward bits n)
      (m.drop (measurementCount ((List.range n).flatMap (fold32Forward bits))))
      (fold32Prefix bits n m s) := by
  simp only [fold32Prefix,List.range_succ,List.flatMap_append,List.flatMap_singleton,run_append,run_take]

private theorem literal_succ (bits : Nat → Bool) (n : Nat) (enabled : Bool) :
    fold32PartialLiteral bits (n+1) enabled=fold32PartialLiteral bits n enabled+
      2^(fold32Starts[n]?.getD 0)*foldBlockLiteral (fold32Cells bits n false) enabled := by
  simp [fold32PartialLiteral,List.range_succ,List.map_append]

private theorem next_boundary (n : Nat) (hn : n<9) :
    fold32Starts[n+1]?.getD 0=fold32Starts[n]?.getD 0+fold32Sizes[n]?.getD 0 := by
  interval_cases n <;> decide

theorem fold32Prefix_control (bits : Nat → Bool) (n : Nat) (hn : n≤10) (s : State) (m : List Bool)
    (ready : Fold32Ready 0 s.basis) : (fold32Prefix bits n m s).basis 0=s.basis 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have inv := fold32_forward_prefix_contract bits n (by omega) s m ready
    rw [prefix_succ]
    exact (fold32_forward_prefix bits n (by omega) (fold32Prefix bits n m s) _ inv.1.1 0
      (Or.inl (by dsimp only [Wire]; omega))).trans (ih (by omega))

/-- Conservation across the prefix, with its live carry read from the
actual shared pool. -/
theorem fold32Prefix_conservation (bits : Nat → Bool) (n : Nat) (hn : n≤9) (s : State) (m : List Bool)
    (ready : Fold32Ready 0 s.basis) :
    regValue fold32Word (fold32Prefix bits n m s).basis+
      2^(fold32Starts[n]?.getD 0)*
        (((fold32Input n).map (fold32Prefix bits n m s).basis).getD false).toNat=
    regValue fold32Word s.basis+fold32PartialLiteral bits n (s.basis 0) := by
  induction n with
  | zero => simp [fold32Prefix,fold32PartialLiteral,fold32Input,run]
  | succ n ih =>
    have prev := ih (by omega)
    have inv := fold32_forward_prefix_contract bits n (by omega) s m ready
    let tape := m.drop (measurementCount ((List.range n).flatMap (fold32Forward bits)))
    have step := fold32_forward_conservation bits n (by omega) (fold32Prefix bits n m s) tape inv.1.1
    have carry := fold32_forward_carry bits n (by omega) (fold32Prefix bits n m s) tape inv.1.1
    have control := fold32Prefix_control bits n (by omega) s m ready
    rw [control] at step
    rw [prefix_succ,literal_succ,next_boundary n (by omega)]
    have input : fold32Input (n+1)=some (258+n) := by
      simp only [fold32Input,show n+1≠0 by omega,if_false]
      congr 1

    rw [input,Option.map_some,Option.getD_some,carry]
    simp only [tape,Nat.mul_add] at step
    omega

/-- The odd literal specified by the ten contiguous blocks. -/
def fold32Literal (bits : Nat → Bool) : Nat := fold32PartialLiteral bits 10 true

private theorem literal_complete (bits : Nat → Bool) (enabled : Bool) :
    fold32PartialLiteral bits 10 enabled=if enabled then fold32Literal bits else 0 := by
  cases enabled
  · simp [fold32PartialLiteral,foldBlockLiteral_disabled]
  · rfl

/-- The whole physical forward sweep adds the specified odd literal
modulo 2^257. All carries come from its actual intermediate states. -/
theorem fold32_forward_word (bits : Nat → Bool) (s : State) (m : List Bool)
    (ready : Fold32Ready 0 s.basis) :
    regValue fold32Word (fold32Prefix bits 10 m s).basis=
      (regValue fold32Word s.basis+(if s.basis 0 then fold32Literal bits else 0))%2^257 := by
  have prev := fold32Prefix_conservation bits 9 (by decide) s m ready
  have inv := fold32_forward_prefix_contract bits 9 (by decide) s m ready
  let tape := m.drop (measurementCount ((List.range 9).flatMap (fold32Forward bits)))
  have step := fold32_forward_conservation bits 9 (by decide) (fold32Prefix bits 9 m s) tape inv.1.1
  rw [fold32Prefix_control bits 9 (by decide) s m ready] at step
  have literal := literal_succ bits 9 (s.basis 0)
  rw [literal_complete] at literal
  have value : regValue fold32Word (fold32Prefix bits 10 m s).basis+
      2^257*(fold32Carry bits 9 (fold32Prefix bits 9 m s).basis).toNat=
      regValue fold32Word s.basis+(if s.basis 0 then fold32Literal bits else 0) := by
    rw [show 10=9+1 from rfl,prefix_succ]
    norm_num only [fold32Starts,fold32Sizes,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some] at prev step literal
    dsimp only [tape] at step
    omega
  have bound : regValue fold32Word (fold32Prefix bits 10 m s).basis<2^257 := by
    simpa only [fold32Word,List.length_range'] using regValue_lt fold32Word (fold32Prefix bits 10 m s).basis
  rw [←value,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]

/-- Complete thirty-two-pool implementation: numeric word, zero scratch,
unchanged control and restored phase, uniformly for every measurement tape. -/
theorem fold32Program_contract (bits : Nat → Bool) (s : State) (m : List Bool)
    (ready : Fold32Ready 0 s.basis) :
    let out := run (fold32Program bits) m s
    regValue fold32Word out.basis=
      (regValue fold32Word s.basis+(if s.basis 0 then fold32Literal bits else 0))%2^257 ∧
    Fold32Ready 0 out.basis ∧ out.basis 0=s.basis 0 ∧ out.phase=s.phase := by
  have cleanup := fold32Program_cleanup bits s m ready
  refine ⟨?_,cleanup.1,?_,cleanup.2.1⟩
  · rw [regValue_congr fold32Word _ (fold32Prefix bits 10 m s).basis (by
      intro q hq
      apply cleanup.2.2
      simp only [fold32Word,List.mem_range'] at hq
      dsimp only [Wire]
      omega)]
    exact fold32_forward_word bits s m ready
  · exact (cleanup.2.2 0 (by decide)).trans (fold32Prefix_control bits 10 (by decide) s m ready)

end ECDSAAdd.Arithmetic.Paper935
