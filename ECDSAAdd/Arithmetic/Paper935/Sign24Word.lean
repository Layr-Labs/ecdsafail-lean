import ECDSAAdd.Arithmetic.Paper935.Sign24Value

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

def sign24Prefix (subtract : Bool) (n : Nat) (m : List Bool) (s : State) : State :=
  run ((List.range n).flatMap (sign24Forward subtract)) m s

def sign24PartialLiteral (subtract : Bool) (n : Nat) (enabled : Bool) : Nat :=
  ((List.range n).map fun j => 2^(sign24Starts[j]?.getD 0)*
    foldBlockLiteral (sign24Cells subtract j false) enabled).sum

private theorem prefix_succ (subtract : Bool) (n : Nat) (m : List Bool) (s : State) :
    sign24Prefix subtract (n+1) m s=run (sign24Forward subtract n)
      (m.drop (measurementCount ((List.range n).flatMap (sign24Forward subtract))))
      (sign24Prefix subtract n m s) := by
  simp only [sign24Prefix,List.range_succ,List.flatMap_append,List.flatMap_singleton,run_append,run_take]

private theorem literal_succ (subtract : Bool) (n : Nat) (enabled : Bool) :
    sign24PartialLiteral subtract (n+1) enabled=sign24PartialLiteral subtract n enabled+
      2^(sign24Starts[n]?.getD 0)*foldBlockLiteral (sign24Cells subtract n false) enabled := by
  simp [sign24PartialLiteral,List.range_succ,List.map_append]

private theorem next_boundary (n : Nat) (hn : n<2) :
    sign24Starts[n+1]?.getD 0=sign24Starts[n]?.getD 0+sign24Sizes[n]?.getD 0 := by
  interval_cases n <;> decide

theorem sign24Prefix_control (subtract : Bool) (n : Nat) (hn : n≤3) (s : State) (m : List Bool)
    (ready : Sign24Ready 0 s.basis) : (sign24Prefix subtract n m s).basis 0=s.basis 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have inv := sign24_forward_prefix_contract subtract n (by omega) s m ready
    rw [prefix_succ]
    exact (sign24_forward_prefix subtract n (by omega) (sign24Prefix subtract n m s) _ inv.1.1 0
      (Or.inl (by dsimp only [Wire]; omega))).trans (ih (by omega))

/-- Conservation across the prefix, with its live carry read from the
actual shared pool. -/
theorem sign24Prefix_conservation (subtract : Bool) (n : Nat) (hn : n≤2) (s : State) (m : List Bool)
    (ready : Sign24Ready 0 s.basis) :
    regValue sign24Word (sign24Prefix subtract n m s).basis+
      2^(sign24Starts[n]?.getD 0)*
        (((sign24Input n).map (sign24Prefix subtract n m s).basis).getD false).toNat=
    regValue sign24Word s.basis+sign24PartialLiteral subtract n (s.basis 0) := by
  induction n with
  | zero => simp [sign24Prefix,sign24PartialLiteral,sign24Input,run]
  | succ n ih =>
    have prev := ih (by omega)
    have inv := sign24_forward_prefix_contract subtract n (by omega) s m ready
    let tape := m.drop (measurementCount ((List.range n).flatMap (sign24Forward subtract)))
    have step := sign24_forward_conservation subtract n (by omega) (sign24Prefix subtract n m s) tape inv.1.1
    have carry := sign24_forward_carry subtract n (by omega) (sign24Prefix subtract n m s) tape inv.1.1
    have control := sign24Prefix_control subtract n (by omega) s m ready
    rw [control] at step
    rw [prefix_succ,literal_succ,next_boundary n (by omega)]
    have input : sign24Input (n+1)=some (59+n) := by
      simp only [sign24Input,show n+1≠0 by omega,if_false]
      congr 1

    rw [input,Option.map_some,Option.getD_some,carry]
    simp only [tape,Nat.mul_add] at step
    omega

private theorem literal_complete (subtract enabled : Bool) :
    sign24PartialLiteral subtract 3 enabled=if enabled then sign24Literal subtract else 0 := by
  cases subtract <;> cases enabled <;> decide

/-- The whole physical forward sweep adds the selected author literal
modulo 2^58. All carries come from its actual intermediate states. -/
theorem sign24_forward_word (subtract : Bool) (s : State) (m : List Bool)
    (ready : Sign24Ready 0 s.basis) :
    regValue sign24Word (sign24Prefix subtract 3 m s).basis=
      (regValue sign24Word s.basis+(if s.basis 0 then sign24Literal subtract else 0))%2^58 := by
  have prev := sign24Prefix_conservation subtract 2 (by decide) s m ready
  have inv := sign24_forward_prefix_contract subtract 2 (by decide) s m ready
  let tape := m.drop (measurementCount ((List.range 2).flatMap (sign24Forward subtract)))
  have step := sign24_forward_conservation subtract 2 (by decide) (sign24Prefix subtract 2 m s) tape inv.1.1
  rw [sign24Prefix_control subtract 2 (by decide) s m ready] at step
  have literal := literal_succ subtract 2 (s.basis 0)
  rw [literal_complete] at literal
  have value : regValue sign24Word (sign24Prefix subtract 3 m s).basis+
      2^58*(sign24Carry subtract 2 (sign24Prefix subtract 2 m s).basis).toNat=
      regValue sign24Word s.basis+(if s.basis 0 then sign24Literal subtract else 0) := by
    rw [show 3=2+1 from rfl,prefix_succ]
    norm_num only [sign24Starts,sign24Sizes,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some] at prev step literal
    dsimp only [tape] at step
    omega
  have bound : regValue sign24Word (sign24Prefix subtract 3 m s).basis<2^58 := by
    simpa only [sign24Word,List.length_range'] using regValue_lt sign24Word (sign24Prefix subtract 3 m s).basis
  rw [←value,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt bound]

/-- Complete twenty-four-pool implementation: numeric word, zero scratch,
unchanged control and restored phase, uniformly for every measurement tape. -/
theorem sign24Program_contract (subtract : Bool) (s : State) (m : List Bool)
    (ready : Sign24Ready 0 s.basis) :
    let out := run (sign24Program subtract) m s
    regValue sign24Word out.basis=
      (regValue sign24Word s.basis+(if s.basis 0 then sign24Literal subtract else 0))%2^58 ∧
    Sign24Ready 0 out.basis ∧ out.basis 0=s.basis 0 ∧ out.phase=s.phase := by
  have cleanup := sign24Program_cleanup subtract s m ready
  refine ⟨?_,cleanup.1,?_,cleanup.2.1⟩
  · rw [regValue_congr sign24Word _ (sign24Prefix subtract 3 m s).basis (by
      intro q hq
      apply cleanup.2.2
      simp only [sign24Word,List.mem_range'] at hq
      dsimp only [Wire]
      omega)]
    exact sign24_forward_word subtract s m ready
  · exact (cleanup.2.2 0 (by decide)).trans (sign24Prefix_control subtract 3 (by decide) s m ready)

end ECDSAAdd.Arithmetic.Paper935
