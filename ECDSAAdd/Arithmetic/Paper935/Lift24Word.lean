import ECDSAAdd.Arithmetic.Paper935.Lift24Value

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def lift24Prefix (subtract : Bool) (n : Nat) (m : List Bool) (s : State) : State :=
  run ((List.range n).flatMap (lift24Forward subtract)) m s

def lift24PartialLiteral (subtract : Bool) (n : Nat) (enabled : Bool) : Nat :=
  ((List.range n).map fun j => 2^(lift24Starts[j]?.getD 0)*
    foldBlockLiteral (lift24Cells subtract j false) enabled).sum

private theorem prefix_succ (subtract : Bool) (n : Nat) (m : List Bool) (s : State) :
    lift24Prefix subtract (n+1) m s=run (lift24Forward subtract n)
      (m.drop (measurementCount ((List.range n).flatMap (lift24Forward subtract))))
      (lift24Prefix subtract n m s) := by
  simp only [lift24Prefix,List.range_succ,List.flatMap_append,List.flatMap_singleton,run_append,run_take]

private theorem literal_succ (subtract : Bool) (n : Nat) (enabled : Bool) :
    lift24PartialLiteral subtract (n+1) enabled=lift24PartialLiteral subtract n enabled+
      2^(lift24Starts[n]?.getD 0)*foldBlockLiteral (lift24Cells subtract n false) enabled := by
  simp [lift24PartialLiteral,List.range_succ,List.map_append]

private theorem next_boundary (n : Nat) (hn : n<2) :
    lift24Starts[n+1]?.getD 0=lift24Starts[n]?.getD 0+lift24Sizes[n]?.getD 0 := by
  interval_cases n <;> decide

theorem lift24Prefix_control (subtract : Bool) (n : Nat) (hn : n≤3) (s : State) (m : List Bool)
    (ready : Lift24Ready 0 s.basis) : (lift24Prefix subtract n m s).basis 0=s.basis 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have inv := lift24_forward_prefix_contract subtract n (by omega) s m ready
    rw [prefix_succ]
    exact (lift24_forward_prefix subtract n (by omega) (lift24Prefix subtract n m s) _ inv.1.1 0
      (Or.inl (by dsimp only [Wire]; omega))).trans (ih (by omega))

/-- Conservation across the prefix, with its live carry read from the
actual shared pool. -/
theorem lift24Prefix_conservation (subtract : Bool) (n : Nat) (hn : n≤2) (s : State) (m : List Bool)
    (ready : Lift24Ready 0 s.basis) :
    regValue lift24Word (lift24Prefix subtract n m s).basis+
      2^(lift24Starts[n]?.getD 0)*
        (((lift24Input n).map (lift24Prefix subtract n m s).basis).getD false).toNat=
    regValue lift24Word s.basis+lift24PartialLiteral subtract n (s.basis 0) := by
  induction n with
  | zero => simp [lift24Prefix,lift24PartialLiteral,lift24Input,run]
  | succ n ih =>
    have prev := ih (by omega)
    have inv := lift24_forward_prefix_contract subtract n (by omega) s m ready
    let tape := m.drop (measurementCount ((List.range n).flatMap (lift24Forward subtract)))
    have step := lift24_forward_conservation subtract n (by omega) (lift24Prefix subtract n m s) tape inv.1.1
    have carry := lift24_forward_carry subtract n (by omega) (lift24Prefix subtract n m s) tape inv.1.1
    have control := lift24Prefix_control subtract n (by omega) s m ready
    rw [control] at step
    rw [prefix_succ,literal_succ,next_boundary n (by omega)]
    have input : lift24Input (n+1)=some (59+n) := by
      simp only [lift24Input,show n+1≠0 by omega,if_false]
      congr 1

    rw [input,Option.map_some,Option.getD_some,carry]
    simp only [tape,Nat.mul_add] at step
    omega

private theorem literal_complete (subtract enabled : Bool) :
    lift24PartialLiteral subtract 3 enabled=if enabled then lift24Literal subtract else 0 := by
  cases subtract <;> cases enabled <;> decide

/-- The whole physical forward sweep adds the selected author literal
modulo 2^58. All carries come from its actual intermediate states. -/
theorem lift24_forward_word (subtract : Bool) (s : State) (m : List Bool)
    (ready : Lift24Ready 0 s.basis) :
    regValue lift24Word (lift24Prefix subtract 3 m s).basis=
      (regValue lift24Word s.basis+(if s.basis 0 then lift24Literal subtract else 0))%2^58 := by
  have prev := lift24Prefix_conservation subtract 2 (by decide) s m ready
  have inv := lift24_forward_prefix_contract subtract 2 (by decide) s m ready
  let tape := m.drop (measurementCount ((List.range 2).flatMap (lift24Forward subtract)))
  have step := lift24_forward_conservation subtract 2 (by decide) (lift24Prefix subtract 2 m s) tape inv.1.1
  rw [lift24Prefix_control subtract 2 (by decide) s m ready] at step
  have literal := literal_succ subtract 2 (s.basis 0)
  rw [literal_complete] at literal
  have value : regValue lift24Word (lift24Prefix subtract 3 m s).basis+
      2^58*(lift24Carry subtract 2 (lift24Prefix subtract 2 m s).basis).toNat=
      regValue lift24Word s.basis+(if s.basis 0 then lift24Literal subtract else 0) := by
    rw [show 3=2+1 from rfl,prefix_succ]
    norm_num only [lift24Starts,lift24Sizes,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some] at prev step literal
    dsimp only [tape] at step
    omega
  have bound : regValue lift24Word (lift24Prefix subtract 3 m s).basis<2^58 := by
    simpa only [lift24Word,List.length_range'] using regValue_lt lift24Word (lift24Prefix subtract 3 m s).basis
  rw [←value,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]

/-- Complete twenty-four-pool implementation: numeric word, zero scratch,
unchanged control and restored phase, uniformly for every measurement tape. -/
theorem lift24Program_contract (subtract : Bool) (s : State) (m : List Bool)
    (ready : Lift24Ready 0 s.basis) :
    let out := run (lift24Program subtract) m s
    regValue lift24Word out.basis=
      (regValue lift24Word s.basis+(if s.basis 0 then lift24Literal subtract else 0))%2^58 ∧
    Lift24Ready 0 out.basis ∧ out.basis 0=s.basis 0 ∧ out.phase=s.phase := by
  have cleanup := lift24Program_cleanup subtract s m ready
  refine ⟨?_,cleanup.1,?_,cleanup.2.1⟩
  · rw [regValue_congr lift24Word _ (lift24Prefix subtract 3 m s).basis (by
      intro q hq
      apply cleanup.2.2
      simp only [lift24Word,List.mem_range'] at hq
      dsimp only [Wire]
      omega)]
    exact lift24_forward_word subtract s m ready
  · exact (cleanup.2.2 0 (by decide)).trans (lift24Prefix_control subtract 3 (by decide) s m ready)

end ECDSAAdd.Arithmetic.Paper935
