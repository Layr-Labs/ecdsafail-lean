import ECDSAAdd.Framework.WireRenamePool
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
namespace ECDSAAdd

/-- Finite physical relabeling transports an actual complete-state equality.
Every physical site outside the two programs' image is preserved. -/
theorem run_rename_eq_of_eq (f : Wire → Wire) (S : Finset Wire)
    (hf : ∀a∈S,∀b∈S,f a=f b → a=b) (P Q : Program)
    (hP : wires P⊆S) (hQ : wires Q⊆S) (m n : List Bool) (t s : State)
    (phase : t.phase=s.phase) (basis : ∀q∈S,t.basis q=s.basis (f q))
    (same : run P m t=run Q n t) :
    run (renameProgram f P) m s=run (renameProgram f Q) n s := by
  have old := run_rename_pool f S hf P hP m t s phase basis
  have fresh := run_rename_pool f S hf Q hQ n t s phase basis
  apply State.extensionality
  · exact old.1.trans ((congrArg State.phase same).trans fresh.1.symm)
  · funext q
    by_cases image : q∈S.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp image
      exact (old.2 a ha).trans ((congrArg (fun v : State => v.basis a) same).trans (fresh.2 a ha).symm)
    · exact (run_rename_pool_outside f S P hP m s q image).trans
        (run_rename_pool_outside f S Q hQ n s q image).symm

end ECDSAAdd
#print axioms ECDSAAdd.run_rename_eq_of_eq
