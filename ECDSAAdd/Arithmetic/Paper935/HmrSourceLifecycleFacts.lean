import ECDSAAdd.Arithmetic.Paper935.HmrSourceLifecyclePrograms
import ECDSAAdd.Arithmetic.Paper935.HmrSourceCallPorts

namespace ECDSAAdd.Arithmetic.Paper935

attribute [local irreducible] s2HmrSourceLayout s6HmrSourceLayout

theorem s2SourceGap_measurements : recordedMeasurementCount s2SourceGap = 340 := by
  decide +kernel

theorem s6SourceGap_measurements : recordedMeasurementCount s6SourceGap = 168 := by
  decide +kernel

theorem s2SourceDemolished_eq : s2SourceDemolished = s2HmrSourceY := by
  decide +kernel

/-- The actual gap ends by measuring the entire multiplier word, on every tape.
This does not assert cleanup of the sign-fix scratch or cancellation of phase. -/
theorem s2SourceGap_demolished (tape : List Bool) (cursor : Nat) (s : State) :
    ∀ q ∈ s2HmrSourceY, (runWithTape s2SourceGap tape cursor s).basis q = false := by
  intro q hq
  unfold s2SourceGap
  rw [runWithTape_append, hmrDemolish_basis]
  rw [s2SourceDemolished_eq]
  simp [hq]

theorem s2SourceGap_cursor : s2SourceGapStart + recordedMeasurementCount s2SourceGap =
    s2SourceGapEnd := by
  rw [s2SourceGap_measurements]
  rfl

theorem s6SourceGap_cursor : s6SourceGapStart + recordedMeasurementCount s6SourceGap =
    s6SourceGapEnd := by
  rw [s6SourceGap_measurements]
  rfl

private def sourceAvoids (qs : List Wire) : RecordedProgram → Bool
  | [] => true
  | .gate (.X q)::P | .gate (.CX _ q)::P | .gate (.CCX _ _ q)::P |
    .gate (.measureX q _ _)::P => decide (q ∉ qs) && sourceAvoids qs P
  | .phaseFromRecord _ _::P => sourceAvoids qs P

private theorem sourceAvoids_iff (qs : List Wire) (P : RecordedProgram) :
    sourceAvoids qs P = true ↔ Disjoint qs.toFinset (hmrBasisWrites P) := by
  induction P with
  | nil => simp [sourceAvoids, hmrBasisWrites]
  | cons i P ih =>
    cases i with
    | gate i => cases i <;> simp [sourceAvoids, hmrBasisWrites, Finset.disjoint_insert_right, ih]
    | phaseFromRecord j cs => simpa [sourceAvoids, hmrBasisWrites] using ih

theorem s2SourceGap_row_disjoint :
    Disjoint s2HmrSourceRow.wires.toFinset (hmrBasisWrites s2SourceGap) := by
  apply (sourceAvoids_iff _ _).mp
  decide +kernel

theorem s6SourceGap_row_disjoint :
    Disjoint s6HmrSourceRow.wires.toFinset (hmrBasisWrites s6SourceGap) := by
  apply (sourceAvoids_iff _ _).mp
  decide +kernel

theorem s2SourceGap_flags_disjoint :
    Disjoint s2HmrSourceLayout.flags (hmrBasisWrites s2SourceGap) := by
  have checked : sourceAvoids [851,804] s2SourceGap = true := by decide +kernel
  have flags : s2HmrSourceLayout.flags = ([851,804] : List Wire).toFinset := by decide +kernel
  rw [flags]
  exact (sourceAvoids_iff _ _).mp checked

attribute [local irreducible] s2SourceGap s6SourceGap s2HmrSourceRow s6HmrSourceRow

theorem s2SourceGap_row_frame (tape : List Bool) (cursor : Nat) (s : State)
    (q : Wire) (hq : q ∈ s2HmrSourceRow.wires) :
    (runWithTape s2SourceGap tape cursor s).basis q = s.basis q :=
  hmr_preserves_outside_writes _ _ _ _ _ (fun hw =>
    Finset.disjoint_left.mp s2SourceGap_row_disjoint (List.mem_toFinset.mpr hq) hw)

theorem s6SourceGap_row_frame (tape : List Bool) (cursor : Nat) (s : State)
    (q : Wire) (hq : q ∈ s6HmrSourceRow.wires) :
    (runWithTape s6SourceGap tape cursor s).basis q = s.basis q :=
  hmr_preserves_outside_writes _ _ _ _ _ (fun hw =>
    Finset.disjoint_left.mp s6SourceGap_row_disjoint (List.mem_toFinset.mpr hq) hw)

theorem s2SourceGap_flags_frame (tape : List Bool) (cursor : Nat) (s : State)
    (q : Wire) (hq : q ∈ s2HmrSourceLayout.flags) :
    (runWithTape s2SourceGap tape cursor s).basis q = s.basis q :=
  hmr_preserves_outside_writes _ _ _ _ _ (fun hw =>
    Finset.disjoint_left.mp s2SourceGap_flags_disjoint hq hw)

theorem s6SourceCorrection_writes : hmrBasisWrites s6SourceCorrection = ∅ := by
  decide +kernel

theorem s6SourceCorrection_basis (tape : List Bool) (cursor : Nat) (s : State)
    (q : Wire) : (runWithTape s6SourceCorrection tape cursor s).basis q = s.basis q := by
  apply hmr_preserves_outside_writes
  rw [s6SourceCorrection_writes]
  exact Finset.notMem_empty q

private def sourceRecordsReady (cursor : Nat) : RecordedProgram → Bool
  | [] => true
  | .gate i :: tail => sourceRecordsReady (cursor + measurementCount [i]) tail
  | .phaseFromRecord j _ :: tail => decide (j < cursor) && sourceRecordsReady cursor tail

private theorem sourceRecordsReady_iff (P : RecordedProgram) (cursor : Nat) :
    sourceRecordsReady cursor P = true ↔ RecordedWellFormedAt cursor P := by
  induction P generalizing cursor with
  | nil => simp [sourceRecordsReady, RecordedWellFormedAt]
  | cons i tail ih =>
    cases i <;> simp [sourceRecordsReady, RecordedWellFormedAt, ih]

theorem s2SourceGap_wellFormed : RecordedWellFormedAt s2SourceGapStart s2SourceGap := by
  apply (sourceRecordsReady_iff _ _).mp
  decide +kernel

theorem s6SourceGap_wellFormed : RecordedWellFormedAt s6SourceGapStart s6SourceGap := by
  apply (sourceRecordsReady_iff _ _).mp
  decide +kernel

end ECDSAAdd.Arithmetic.Paper935
