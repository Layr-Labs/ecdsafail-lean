import ECDSAAdd.Arithmetic.Paper935.Fold16Invariant

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

theorem fold16_forward_prefix_contract (subtract : Bool) (n : Nat) (hn : n≤4)
    (s : State) (m : List Bool) (ready : Fold16Ready 0 s.basis) :
    let t := run ((List.range n).flatMap (fold16Forward subtract)) m s
    Fold16Invariant subtract n t.basis ∧ t.phase=s.phase := by
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
    · exact fold16_forward_invariant subtract n (by omega) _ _ previous.1
    · exact (fold16_forward_phase subtract n (by omega) _ _ previous.1.1).trans previous.2

theorem fold16_all_forward_contract (subtract : Bool) (s : State) (m : List Bool)
    (ready : Fold16Ready 0 s.basis) :
    let t := run ((List.range 5).flatMap (fold16Forward subtract)) m s
    Fold16Invariant subtract 4 t.basis ∧ t.phase=s.phase := by
  have previous := fold16_forward_prefix_contract subtract 4 (by decide) s m ready
  rw [show 5=4+1 from rfl,List.range_succ,List.flatMap_append,List.flatMap_singleton]
  dsimp only
  rw [run_append,run_take]
  exact ⟨fold16_last_invariant subtract _ _ previous.1,
    (fold16_forward_phase subtract 4 (by decide) _ _ previous.1.1).trans previous.2⟩

theorem fold16_reverse_contract (subtract : Bool) (n : Nat) (hn : n≤4)
    (s : State) (m : List Bool) (inv : Fold16Invariant subtract n s.basis) :
    let t := run ((List.range n).reverse.flatMap (fold16Erase subtract)) m s
    Fold16Ready 0 t.basis ∧ t.phase=s.phase ∧ ∀ q<59,t.basis q=s.basis q := by
  induction n generalizing s m with
  | zero =>
    exact ⟨inv.1,rfl,by intro q hq; rfl⟩
  | succ n ih =>
    have result := fold16_erase_run subtract n (by omega) s m inv
    have next := fold16_erase_invariant subtract n (by omega) s m inv
    have tailResult := ih (by omega) (run (fold16Erase subtract n) m s)
      (m.drop (measurementCount (fold16Erase subtract n))) next
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

/-- The complete shared-pool fold clears all sixteen work lines and restores
the initial phase for every tape. Reverse keeper cleanup preserves every
control/data address, so numerical output is the forward sweep's output. -/
theorem fold16Program_cleanup (subtract : Bool) (s : State) (m : List Bool)
    (ready : Fold16Ready 0 s.basis) :
    let t := run (fold16Program subtract) m s
    Fold16Ready 0 t.basis ∧ t.phase=s.phase ∧ ∀ q<59,
      t.basis q=(run ((List.range 5).flatMap (fold16Forward subtract)) m s).basis q := by
  have forward := fold16_all_forward_contract subtract s m ready
  have backward := fold16_reverse_contract subtract 4 (by decide)
    (run ((List.range 5).flatMap (fold16Forward subtract)) m s)
    (m.drop (measurementCount ((List.range 5).flatMap (fold16Forward subtract)))) forward.1
  dsimp only
  rw [fold16Program,run_append,run_take]
  exact ⟨backward.1,backward.2.1.trans forward.2,backward.2.2⟩

end ECDSAAdd.Arithmetic.Paper935
