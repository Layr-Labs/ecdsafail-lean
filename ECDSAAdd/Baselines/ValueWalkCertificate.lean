import ECDSAAdd.Baselines.ValueWalkSlots
import ECDSAAdd.Baselines.ValueWalkPhysical

namespace ECDSAAdd.Baselines
open Challenge

/-- Uniform, kernel-proved bounds; slot count is conservative, not an exact score. -/
def valueWalkBounds : Bounds := ⟨6286806, 3779274, 3134, 61000000⟩

/-- Complete fixed-encoding certificate, with no producer or resource hypotheses. -/
theorem valueWalkCertificate : Certificate normalizedValueWalk valueWalkBounds where
  correct := normalizedValueWalk_correct
  physical := normalizedValueWalk_physical
  toffoli_le C := (normalize_toffoli _).trans (valueWalk_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (valueWalk C)) ≤ 3779274
    rw [normalize_measurements]
    exact valueWalk_measurements C
  qubits_le := normalizedValueWalk_qubits
  gateSlots_le := normalizedValueWalk_gateSlots_le

end ECDSAAdd.Baselines
