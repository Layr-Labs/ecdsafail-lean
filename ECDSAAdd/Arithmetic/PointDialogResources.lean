import ECDSAAdd.Arithmetic.PointDialogIntegration
import ECDSAAdd.Arithmetic.CompactPointFiniteSupport

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- Physical support is bounded by the original caller footprint; this is not a peak-live proof. -/
theorem pointDialogFinite_qubits (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cx cy : Fp) : qubitCount (pointDialogFinite L C cx cy)≤2068 := by
  have sup := pointDialogFinite_compact_wires L hw hn C cx cy
  have h := Finset.card_le_card sup
  rw [List.toFinset_card_of_nodup (L.compactPointSites_nodup hw hn),
    L.compactPointSites_length hw] at h
  exact h

end ECDSAAdd.Arithmetic
