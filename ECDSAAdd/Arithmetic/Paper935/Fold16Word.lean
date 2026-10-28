import ECDSAAdd.Arithmetic.Paper935.Fold16Value

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def fold16Prefix (subtract : Bool) (n : Nat) (m : List Bool) (s : State) : State :=
  run ((List.range n).flatMap (fold16Forward subtract)) m s

def fold16PartialLiteral (subtract : Bool) (n : Nat) (enabled : Bool) : Nat :=
  ((List.range n).map fun j => 2^(fold16Starts[j]?.getD 0)*
    foldBlockLiteral (fold16Cells subtract j false) enabled).sum

private theorem prefix_succ (subtract : Bool) (n : Nat) (m : List Bool) (s : State) :
    fold16Prefix subtract (n+1) m s=run (fold16Forward subtract n)
      (m.drop (measurementCount ((List.range n).flatMap (fold16Forward subtract))))
      (fold16Prefix subtract n m s) := by
  simp only [fold16Prefix,List.range_succ,List.flatMap_append,List.flatMap_singleton,run_append,run_take]

private theorem literal_succ (subtract : Bool) (n : Nat) (enabled : Bool) :
    fold16PartialLiteral subtract (n+1) enabled=fold16PartialLiteral subtract n enabled+
      2^(fold16Starts[n]?.getD 0)*foldBlockLiteral (fold16Cells subtract n false) enabled := by
  simp [fold16PartialLiteral,List.range_succ,List.map_append]

private theorem next_boundary (n : Nat) (hn : n<4) :
    fold16Starts[n+1]?.getD 0=fold16Starts[n]?.getD 0+fold16Sizes[n]?.getD 0 := by
  interval_cases n <;> decide

theorem fold16Prefix_control (subtract : Bool) (n : Nat) (hn : n≤5) (s : State) (m : List Bool)
    (ready : Fold16Ready 0 s.basis) : (fold16Prefix subtract n m s).basis 0=s.basis 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have inv := fold16_forward_prefix_contract subtract n (by omega) s m ready
    rw [prefix_succ]
    exact (fold16_forward_prefix subtract n (by omega) (fold16Prefix subtract n m s) _ inv.1.1 0
      (Or.inl (by dsimp only [Wire]; omega))).trans (ih (by omega))

/-- Conservation across the prefix, with its live carry read from the
actual shared pool. -/
theorem fold16Prefix_conservation (subtract : Bool) (n : Nat) (hn : n≤4) (s : State) (m : List Bool)
    (ready : Fold16Ready 0 s.basis) :
    regValue fold16Word (fold16Prefix subtract n m s).basis+
      2^(fold16Starts[n]?.getD 0)*
        (((fold16Input n).map (fold16Prefix subtract n m s).basis).getD false).toNat=
    regValue fold16Word s.basis+fold16PartialLiteral subtract n (s.basis 0) := by
  induction n with
  | zero => simp [fold16Prefix,fold16PartialLiteral,fold16Input,run]
  | succ n ih =>
    have prev := ih (by omega)
    have inv := fold16_forward_prefix_contract subtract n (by omega) s m ready
    let tape := m.drop (measurementCount ((List.range n).flatMap (fold16Forward subtract)))
    have step := fold16_forward_conservation subtract n (by omega) (fold16Prefix subtract n m s) tape inv.1.1
    have carry := fold16_forward_carry subtract n (by omega) (fold16Prefix subtract n m s) tape inv.1.1
    have control := fold16Prefix_control subtract n (by omega) s m ready
    rw [control] at step
    rw [prefix_succ,literal_succ,next_boundary n (by omega)]
    have input : fold16Input (n+1)=some (59+n) := by
      simp only [fold16Input,show n+1≠0 by omega,if_false]
      congr 1

    rw [input,Option.map_some,Option.getD_some,carry]
    simp only [tape,Nat.mul_add] at step
    omega

private theorem literal_complete (subtract enabled : Bool) :
    fold16PartialLiteral subtract 5 enabled=if enabled then fold16Literal subtract else 0 := by
  cases subtract <;> cases enabled <;> decide

/-- The whole physical forward sweep adds the selected author literal
modulo 2^58. All carries come from its actual intermediate states. -/
theorem fold16_forward_word (subtract : Bool) (s : State) (m : List Bool)
    (ready : Fold16Ready 0 s.basis) :
    regValue fold16Word (fold16Prefix subtract 5 m s).basis=
      (regValue fold16Word s.basis+(if s.basis 0 then fold16Literal subtract else 0))%2^58 := by
  have prev := fold16Prefix_conservation subtract 4 (by decide) s m ready
  have inv := fold16_forward_prefix_contract subtract 4 (by decide) s m ready
  let tape := m.drop (measurementCount ((List.range 4).flatMap (fold16Forward subtract)))
  have step := fold16_forward_conservation subtract 4 (by decide) (fold16Prefix subtract 4 m s) tape inv.1.1
  rw [fold16Prefix_control subtract 4 (by decide) s m ready] at step
  have literal := literal_succ subtract 4 (s.basis 0)
  rw [literal_complete] at literal
  have value : regValue fold16Word (fold16Prefix subtract 5 m s).basis+
      2^58*(fold16Carry subtract 4 (fold16Prefix subtract 4 m s).basis).toNat=
      regValue fold16Word s.basis+(if s.basis 0 then fold16Literal subtract else 0) := by
    rw [show 5=4+1 from rfl,prefix_succ]
    norm_num only [fold16Starts,fold16Sizes,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some] at prev step literal
    dsimp only [tape] at step
    omega
  have bound : regValue fold16Word (fold16Prefix subtract 5 m s).basis<2^58 := by
    simpa only [fold16Word,List.length_range'] using regValue_lt fold16Word (fold16Prefix subtract 5 m s).basis
  rw [←value,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]

/-- Complete sixteen-pool implementation: numeric word, zero scratch,
unchanged control and restored phase, uniformly for every measurement tape. -/
theorem fold16Program_contract (subtract : Bool) (s : State) (m : List Bool)
    (ready : Fold16Ready 0 s.basis) :
    let out := run (fold16Program subtract) m s
    regValue fold16Word out.basis=
      (regValue fold16Word s.basis+(if s.basis 0 then fold16Literal subtract else 0))%2^58 ∧
    Fold16Ready 0 out.basis ∧ out.basis 0=s.basis 0 ∧ out.phase=s.phase := by
  have cleanup := fold16Program_cleanup subtract s m ready
  refine ⟨?_,cleanup.1,?_,cleanup.2.1⟩
  · rw [regValue_congr fold16Word _ (fold16Prefix subtract 5 m s).basis (by
      intro q hq
      apply cleanup.2.2
      simp only [fold16Word,List.mem_range'] at hq
      dsimp only [Wire]
      omega)]
    exact fold16_forward_word subtract s m ready
  · exact (cleanup.2.2 0 (by decide)).trans (fold16Prefix_control subtract 5 (by decide) s m ready)

end ECDSAAdd.Arithmetic.Paper935
