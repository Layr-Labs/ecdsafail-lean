import ECDSAAdd.Arithmetic.Paper935.WalkSeed

namespace ECDSAAdd.Arithmetic.Paper935

/-- Undo the real seed gates in reverse stage order. -/
def unseedWalk (p : Nat) : Program := seedWalkMetadata++seedRows p

theorem seedWalkMetadata_roundtrip (s : State) (m n : List Bool) :
    run seedWalkMetadata n (run seedWalkMetadata m s)=s := by
  cases s with
  | mk phase basis =>
    simp [seedWalkMetadata,run,writeBit]

theorem seedWalk_roundtrip (p : Nat) (hp : p<2^256) (s : State) (m n : List Bool) :
    run (unseedWalk p) n (run (seedWalk p) m s)=s := by
  rw [unseedWalk,seedWalk,run_append,run_append,run_take,run_take]
  rw [seedWalkMetadata_roundtrip]
  exact seed_roundtrip p hp s m _

theorem seedWalk_measurements (p : Nat) : measurementCount (seedWalk p)=0 := by
  simp [seedWalk,measurementCount_append,(seed_counts p).2,seedWalkMetadata,measurementCount]

end ECDSAAdd.Arithmetic.Paper935
