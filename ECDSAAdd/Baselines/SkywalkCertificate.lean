import ECDSAAdd.Baselines.SkywalkSlots
import ECDSAAdd.Baselines.SkywalkPhysical

namespace ECDSAAdd.Baselines
open Challenge

/-- Uniform kernel-proved bounds. Total slots count both measurement corrections. -/
def skywalkBounds : Bounds := ⟨2217386, 1557928, 1899, 47000000⟩

/-- Complete fixed-encoding Skywalk certificate for every public addend. -/
theorem skywalkCertificate : Certificate normalizedSkywalk skywalkBounds where
  correct := normalizedSkywalk_correct
  physical := normalizedSkywalk_physical
  toffoli_le C := (normalize_toffoli _).trans (skywalk_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (skywalk C)) ≤ 1557928
    rw [normalize_measurements]
    exact skywalk_measurements C
  qubits_le := normalizedSkywalk_qubits
  gateSlots_le := normalizedSkywalk_gateSlots_le

end ECDSAAdd.Baselines
