import ECDSAAdd.Arithmetic.Paper935.FusedPlacedExecution

namespace ECDSAAdd.Arithmetic.Paper935
attribute [local irreducible] fusedMagnitudeLift fusedRowFoldSource

private theorem placed_roundtrip (f : Wire → Wire) (S : Finset Wire)
    (inj : Set.InjOn f S) (P Q : Program) (hp : wires P⊆S) (hq : wires Q⊆S)
    (s : State) (m n : List Bool)
    (restored : run Q n (run P m (pullState f s))=pullState f s) :
    run (renameProgram f Q) n (run (renameProgram f P) m s)=s := by
  have first := run_rename_pool f S inj P hp m (pullState f s) s rfl (fun _ _ => rfl)
  have second := run_rename_pool f S inj Q hq n
    (run P m (pullState f s)) (run (renameProgram f P) m s)
    first.1.symm (fun q h => (first.2 q h).symm)
  apply State.extensionality
  · simpa only [pullState] using second.1.trans (congrArg State.phase restored)
  · funext q
    by_cases inside : q∈S.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp inside
      exact (second.2 a ha).trans (congrArg (fun t : State => t.basis a) restored)
    · exact (run_rename_pool_outside f S Q hq n _ q inside).trans
        (run_rename_pool_outside f S P hp m s q inside)

/-- Inverse lift restores the entire physical state, including phase, from
its forward output. The two measurement tapes are independent. -/
theorem placedMagnitude_roundtrip (f : Wire → Wire)
    (inj : Set.InjOn f (Finset.range 305)) (s : State) (m n : List Bool)
    (clean : ∀ i<24,s.basis (f (281+i))=false) :
    run (placedMagnitude f true) n (run (placedMagnitude f false) m s)=s :=
  placed_roundtrip f _ inj _ _ (fusedMagnitudeLift_support false)
    (fusedMagnitudeLift_support true) s m n
    (fusedMagnitudeLift_roundtrip (pullState f s) m n clean)

/-- The source-order inverse fold restores all physical wires. This identity
is unconditional and therefore also applies to parked folded rows. -/
theorem placedRowFold_roundtrip (f : Wire → Wire)
    (inj : Set.InjOn f (Finset.range 537)) (s : State) (m n : List Bool) :
    run (placedRowFold f true) n (run (placedRowFold f false) m s)=s :=
  placed_roundtrip f _ inj _ _ (fusedRowFoldSource_resources false).1
    (fusedRowFoldSource_resources true).1 s m n
    (fusedRowFoldSource_roundtrip (pullState f s) m n)

end ECDSAAdd.Arithmetic.Paper935
