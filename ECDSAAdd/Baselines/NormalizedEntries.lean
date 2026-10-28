import ECDSAAdd.Baselines.Normalize
import ECDSAAdd.Baselines.Qubits

namespace ECDSAAdd.Baselines
open Challenge Secp256k1

/-- Skywalk with same-wire CZ and repeated-control CCX normalized. -/
def normalizedSkywalk : Entry := fun C => normalizeProgram (skywalk C)
/-- ValueWalk with same-wire CZ and repeated-control CCX normalized. -/
def normalizedValueWalk : Entry := fun C => normalizeProgram (valueWalk C)

theorem normalizedSkywalk_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (normalizedSkywalk C) (encodes b (if b then R+C else R)) :=
  (normalize_triple _ _ _).mpr (skywalk_correct C b R)

theorem normalizedValueWalk_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (normalizedValueWalk C) (encodes b (if b then R+C else R)) :=
  (normalize_triple _ _ _).mpr (valueWalk_correct C b R)

theorem normalizedSkywalk_toffoli_exact (C : Point) :
    toffoliCount (normalizedSkywalk C) + repeatedControls (skywalk C) =
      toffoliCount (skywalk C) := normalize_toffoli_exact _

theorem normalizedValueWalk_toffoli_exact (C : Point) :
    toffoliCount (normalizedValueWalk C) + repeatedControls (valueWalk C) =
      toffoliCount (valueWalk C) := normalize_toffoli_exact _

theorem normalizedSkywalk_qubits (C : Point) : qubits (normalizedSkywalk C) ≤ 1899 := by
  rw [normalizedSkywalk, normalize_qubits]
  exact skywalk_qubits C

theorem normalizedValueWalk_qubits (C : Point) : qubits (normalizedValueWalk C) ≤ 3134 := by
  rw [normalizedValueWalk, normalize_qubits]
  exact valueWalk_qubits C

end ECDSAAdd.Baselines
