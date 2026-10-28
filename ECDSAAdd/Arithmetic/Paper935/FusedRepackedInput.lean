import ECDSAAdd.Arithmetic.Paper935.FusedSignedPlacement
import ECDSAAdd.Arithmetic.Paper935.FusedSourceRepack

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- Both payload and sign follow the actual swap journal. -/
def repackedRow (ms : List (Wire × Wire)) (r : WindowRow) : WindowRow :=
  ⟨repackView ms r.payload,repackEquiv ms r.sign⟩

private theorem repack_regValue (ms : List (Wire × Wire))
    (valid : ∀p∈ms,p.1≠p.2) (xs : List Wire) (s : State) (m : List Bool) :
    regValue (xs.map (repackEquiv ms)) (run (repack ms) m s).basis=regValue xs s.basis := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    change (if (run (repack ms) m s).basis (repackEquiv ms q) then 1 else 0)+
      2*regValue (qs.map (repackEquiv ms)) (run (repack ms) m s).basis =
      (if s.basis q then 1 else 0)+2*regValue qs s.basis
    rw [repack_basis ms valid s m q,ih]

/-- Relocation preserves the signed arithmetic value, not only zero bits. -/
theorem repackedRow_value (ms : List (Wire × Wire))
    (valid : ∀p∈ms,p.1≠p.2) (r : WindowRow) (s : State) (m : List Bool) :
    (repackedRow ms r).value (run (repack ms) m s).basis=r.value s.basis := by
  unfold WindowRow.value WindowRow.wires signedRegValue repackedRow
  simp only [repackView_eq_map,←List.map_singleton,←List.map_append,List.length_map]
  rw [repack_regValue ms valid]

/-- A signed coefficient before repacking supplies the actual lift's encoding
at the relocated ports. The journal is executed, not merely renamed on paper. -/
theorem repackedMagnitude_encoding (ms : List (Wire × Wire))
    (valid : ∀p∈ms,p.1≠p.2) (r : WindowRow) (pool : List Wire)
    (s : State) (m : List Bool) (z : Int) (len : r.payload.length=280)
    (encoded : r.value s.basis=z) :
    MagnitudeEncodes z (fun q => (run (repack ms) m s).basis
      (fusedPlacementMap ((repackedRow ms r).sign::(repackedRow ms r).payload++pool) q)) := by
  apply placedMagnitude_encoding
  · simpa only [repackedRow,repackView_length] using len
  · exact (repackedRow_value ms valid r s m).trans encoded

/-- The pinned source s2 journal preserves the signed input encoding. -/
theorem s2RepackedMagnitude_encoding (r : WindowRow) (pool : List Wire)
    (s : State) (m : List Bool) (z : Int) (len : r.payload.length=280)
    (encoded : r.value s.basis=z) :
    MagnitudeEncodes z (fun q => (run (repack s2SourceRepack) m s).basis
      (fusedPlacementMap ((repackedRow s2SourceRepack r).sign::
        (repackedRow s2SourceRepack r).payload++pool) q)) :=
  repackedMagnitude_encoding s2SourceRepack
    (fun p hp => (s2SourceRepack_valid p hp).1) r pool s m z len encoded

/-- The pinned source s6 journal preserves the signed input encoding. -/
theorem s6RepackedMagnitude_encoding (r : WindowRow) (pool : List Wire)
    (s : State) (m : List Bool) (z : Int) (len : r.payload.length=280)
    (encoded : r.value s.basis=z) :
    MagnitudeEncodes z (fun q => (run (repack s6SourceRepack) m s).basis
      (fusedPlacementMap ((repackedRow s6SourceRepack r).sign::
        (repackedRow s6SourceRepack r).payload++pool) q)) :=
  repackedMagnitude_encoding s6SourceRepack
    (fun p hp => (s6SourceRepack_valid p hp).1) r pool s m z len encoded

end ECDSAAdd.Arithmetic.Paper935
