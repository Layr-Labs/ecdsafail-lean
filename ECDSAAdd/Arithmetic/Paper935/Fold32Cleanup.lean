import ECDSAAdd.Arithmetic.Paper935.Fold32Invariant

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

theorem fold32_forward_prefix_contract (bits : Nat → Bool) (n : Nat) (hn : n≤9)
    (s : State) (m : List Bool) (ready : Fold32Ready 0 s.basis) :
    let t := run ((List.range n).flatMap (fold32Forward bits)) m s
    Fold32Invariant bits n t.basis ∧ t.phase=s.phase := by
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
    · exact fold32_forward_invariant bits n (by omega) _ _ previous.1
    · exact (fold32_forward_phase bits n (by omega) _ _ previous.1.1).trans previous.2

theorem fold32_all_forward_contract (bits : Nat → Bool) (s : State) (m : List Bool)
    (ready : Fold32Ready 0 s.basis) :
    let t := run ((List.range 10).flatMap (fold32Forward bits)) m s
    Fold32Invariant bits 9 t.basis ∧ t.phase=s.phase := by
  have previous := fold32_forward_prefix_contract bits 9 (by decide) s m ready
  rw [show 10=9+1 from rfl,List.range_succ,List.flatMap_append,List.flatMap_singleton]
  dsimp only
  rw [run_append,run_take]
  exact ⟨fold32_last_invariant bits _ _ previous.1,
    (fold32_forward_phase bits 9 (by decide) _ _ previous.1.1).trans previous.2⟩

theorem fold32_reverse_contract (bits : Nat → Bool) (n : Nat) (hn : n≤9)
    (s : State) (m : List Bool) (inv : Fold32Invariant bits n s.basis) :
    let t := run ((List.range n).reverse.flatMap (fold32Erase bits)) m s
    Fold32Ready 0 t.basis ∧ t.phase=s.phase ∧ ∀ q<258,t.basis q=s.basis q := by
  induction n generalizing s m with
  | zero =>
    exact ⟨inv.1,rfl,by intro q hq; rfl⟩
  | succ n ih =>
    have result := fold32_erase_run bits n (by omega) s m inv
    have next := fold32_erase_invariant bits n (by omega) s m inv
    have tailResult := ih (by omega) (run (fold32Erase bits n) m s)
      (m.drop (measurementCount (fold32Erase bits n))) next
    rw [List.range_succ,List.reverse_append,List.reverse_singleton,List.singleton_append,
      List.flatMap_cons]
    dsimp only
    rw [run_append,run_take]
    refine ⟨tailResult.1,?_,?_⟩
    · rw [tailResult.2.1,result]
    · intro q hq
      rw [tailResult.2.2 q hq,result]
      have away : q≠258+n := by dsimp only [Wire] at *; omega
      simp only [writeBit,Function.update_of_ne away]

/-- The complete shared-pool fold clears all thirty-two work lines and restores
the initial phase for every tape. Reverse keeper cleanup preserves every
control/data address, so numerical output is the forward sweep's output. -/
theorem fold32Program_cleanup (bits : Nat → Bool) (s : State) (m : List Bool)
    (ready : Fold32Ready 0 s.basis) :
    let t := run (fold32Program bits) m s
    Fold32Ready 0 t.basis ∧ t.phase=s.phase ∧ ∀ q<258,
      t.basis q=(run ((List.range 10).flatMap (fold32Forward bits)) m s).basis q := by
  have forward := fold32_all_forward_contract bits s m ready
  have backward := fold32_reverse_contract bits 9 (by decide)
    (run ((List.range 10).flatMap (fold32Forward bits)) m s)
    (m.drop (measurementCount ((List.range 10).flatMap (fold32Forward bits)))) forward.1
  dsimp only
  rw [fold32Program,run_append,run_take]
  exact ⟨backward.1,backward.2.1.trans forward.2,backward.2.2⟩

end ECDSAAdd.Arithmetic.Paper935
