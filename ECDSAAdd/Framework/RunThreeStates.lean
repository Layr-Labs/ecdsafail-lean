import ECDSAAdd.Framework.WireRename
namespace ECDSAAdd
attribute [local irreducible] run

/-- Measured composition uses independent records for each real stage.
The supplied relation is proved from the three executed stage equations. -/
theorem run_three_states (p q r : Program) (P : State → State → Prop)
    (h : ∀ (s s1 s2 s3 : State) (m1 m2 m3 : List Bool),
      run p m1 s=s1 → run q m2 s1=s2 → run r m3 s2=s3 → P s s3)
    (s : State) (m : List Bool) : P s (run (p++(q++r)) m s) := by
  simp only [run_append]
  apply h s _ _ _ _ _ _ <;> rfl
end ECDSAAdd
#print axioms ECDSAAdd.run_three_states
