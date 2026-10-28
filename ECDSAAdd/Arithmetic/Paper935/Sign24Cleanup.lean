import ECDSAAdd.Arithmetic.Paper935.Sign24Invariant

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

theorem sign24_forward_prefix_contract (subtract : Bool) (n : Nat) (hn : n≤2)
    (s : State) (m : List Bool) (ready : Sign24Ready 0 s.basis) :
    let t := run ((List.range n).flatMap (sign24Forward subtract)) m s
    Sign24Invariant subtract n t.basis ∧ t.phase=s.phase := by
  induction n generalizing s m with
  | zero =>
    constructor
    · exact ⟨ready,by intro i hi; omega⟩
    · rfl
  | succ n ih =>
    have previous := ih (by omega) s m ready
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
    dsimp only
    rw [run_append,run_take]
    constructor
    · exact sign24_forward_invariant subtract n (by omega) _ _ previous.1
    · exact (sign24_forward_phase subtract n (by omega) _ _ previous.1.1).trans previous.2

theorem sign24_all_forward_contract (subtract : Bool) (s : State) (m : List Bool)
    (ready : Sign24Ready 0 s.basis) :
    let t := run ((List.range 3).flatMap (sign24Forward subtract)) m s
    Sign24Invariant subtract 2 t.basis ∧ t.phase=s.phase := by
  have previous := sign24_forward_prefix_contract subtract 2 (by decide) s m ready
  rw [show 3=2+1 from rfl,List.range_succ,List.flatMap_append,List.flatMap_singleton]
  dsimp only
  rw [run_append,run_take]
  exact ⟨sign24_last_invariant subtract _ _ previous.1,
    (sign24_forward_phase subtract 2 (by decide) _ _ previous.1.1).trans previous.2⟩

theorem sign24_reverse_contract (subtract : Bool) (n : Nat) (hn : n≤2)
    (s : State) (m : List Bool) (inv : Sign24Invariant subtract n s.basis) :
    let t := run ((List.range n).reverse.flatMap (sign24Erase subtract)) m s
    Sign24Ready 0 t.basis ∧ t.phase=s.phase ∧ ∀ q<59,t.basis q=s.basis q := by
  induction n generalizing s m with
  | zero =>
    exact ⟨inv.1,rfl,by intro q hq; rfl⟩
  | succ n ih =>
    have result := sign24_erase_run subtract n (by omega) s m inv
    have next := sign24_erase_invariant subtract n (by omega) s m inv
    have tailResult := ih (by omega) (run (sign24Erase subtract n) m s)
      (m.drop (measurementCount (sign24Erase subtract n))) next
    rw [List.range_succ,List.reverse_append,List.reverse_singleton,List.singleton_append,
      List.flatMap_cons]
    dsimp only
    rw [run_append,run_take]
    refine ⟨tailResult.1,?_,?_⟩
    · rw [tailResult.2.1,result]
    · intro q hq
      rw [tailResult.2.2 q hq,result]
      have away : q≠59+n := by dsimp only [Wire] at *; omega
      simp only [writeBit,Function.update_of_ne away]

/-- The complete shared-pool fold clears all twenty-four work lines and restores
the initial phase for every tape. Reverse keeper cleanup preserves every
control/data address, so numerical output is the forward sweep's output. -/
theorem sign24Program_cleanup (subtract : Bool) (s : State) (m : List Bool)
    (ready : Sign24Ready 0 s.basis) :
    let t := run (sign24Program subtract) m s
    Sign24Ready 0 t.basis ∧ t.phase=s.phase ∧ ∀ q<59,
      t.basis q=(run ((List.range 3).flatMap (sign24Forward subtract)) m s).basis q := by
  have forward := sign24_all_forward_contract subtract s m ready
  have backward := sign24_reverse_contract subtract 2 (by decide)
    (run ((List.range 3).flatMap (sign24Forward subtract)) m s)
    (m.drop (measurementCount ((List.range 3).flatMap (sign24Forward subtract)))) forward.1
  dsimp only
  rw [sign24Program,run_append,run_take]
  exact ⟨backward.1,backward.2.1.trans forward.2,backward.2.2⟩

end ECDSAAdd.Arithmetic.Paper935
