import ECDSAAdd.Submission.Entrant.Program

/-! Entrant: Skywalk with flag-only infinity tests (see `ZeroFlag.lean`).
All semantics and metric definitions remain in the protected challenge. -/
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 Challenge Baselines

/-- Infinity addend emits no gates; a finite addend runs `finiteProgram`. -/
def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ => finiteProgram layout C cx cy

def entry : Challenge.Entry := fun C => normalizeProgram (program C)

def bounds : Challenge.Bounds := ⟨2212778, 1553319, 1899, 47000000⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program, run, ← WeierstrassCurve.Affine.Point.zero_def, add_zero, ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    exact fixed_correct _ b R _ (finiteProgram_full_spec layout layout_widths layout_nodup R hc b)
      ((finiteProgram_support layout layout_widths layout_nodup _ cx cy).trans
        (sites_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2212778 := by
  cases C with
  | zero => simp [program, toffoliCount]
  | @some cx cy hc => exact (finiteProgram_counts layout layout_widths layout_nodup _ cx cy).1

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1553319 := by
  cases C with
  | zero => simp [program, measurementCount]
  | @some cx cy hc => exact (finiteProgram_counts layout layout_widths layout_nodup _ cx cy).2.le

theorem program_qubits (C : Point) : qubits (program C) ≤ 1899 := by
  cases C with
  | zero =>
    change qubits [] ≤ 1899
    rw [qubits_empty]
    decide
  | @some cx cy hc =>
    have support := finiteProgram_support layout layout_widths layout_nodup (.some hc) cx cy
    have card := Finset.card_le_card (Finset.union_subset io_subset_sites support)
    have length : (CompressedPointDialog.sites layout).length = 1899 := by
      rw [CompressedPointDialog.sites, List.length_append,
        CompressedPointSquare.residents_length layout layout_widths,
        CompressedPointSquare.sharedPool_length]
    exact card.trans ((List.toFinset_card_le _).trans_eq length)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program, GatePhysical]
  | @some cx cy hc => exact finiteProgram_physical layout layout_widths layout_nodup _ cx cy

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 47000000 := by
  cases C with
  | zero => simp [program, gateSlots]
  | @some cx cy hc => exact finiteProgram_gateSlots_le layout layout_widths _ cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1553319
    rw [normalize_measurements]
    exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1899
    rw [normalize_qubits]
    exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 47000000
    rw [normalize_slots]
    exact program_gateSlots C

end ECDSAAdd.Entrant
