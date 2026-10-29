import ECDSAAdd.Submission.Entrant.RepairFlagAvoid

/-! Entrant: Skywalk with flag-only infinity tests (`ZeroFlag.lean`), short and
paired point comparisons (`ShortEqual.lean`, `PairEqual.lean`), compare-first
constant additions (`FastConst.lean`, `FastGeneric.lean`), enable-free
classification (`EKFree.lean`), and a static site bound that excludes the sites
no block touches (`ArithAvoid.lean`, `QSupport.lean`, `EKSupport.lean`).
All semantics and metric definitions remain in the protected challenge. -/
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 Challenge Baselines

/-- Infinity addend emits no gates; a finite addend runs `finiteProgramN`
around the compare-first generic-branch block. -/
def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      finiteProgramN layout C cy (fastGeneric2 layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)

def bounds : Challenge.Bounds := ⟨2176915, 1517467, 1891, 47000000⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program, run, ← WeierstrassCurve.Affine.Point.zero_def, add_zero, ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have hG := fastGenericG layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _ (finiteProgramN_full_spec layout layout_widths layout_nodup R hc b _
        (fastGeneric_ok layout layout_widths layout_nodup hc) hG)
      ((finiteProgramN_support layout layout_widths layout_nodup _ cy _ hG).trans
        (sitesN_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C) ≤ 2176915 := by
  cases C with
  | zero => simp [program, toffoliCount]
  | @some cx cy hc =>
    have h := (finiteProgramN_counts layout layout_widths (.some hc) cy
      (fastGeneric2 layout cx cy) hc rfl).1
    have g := (fastGeneric2_counts layout layout_widths cx cy).1
    change toffoliCount (finiteProgramN layout (.some hc) cy (fastGeneric2 layout cx cy)) ≤ _
    omega

theorem program_measurements (C : Point) : measurementCount (program C) ≤ 1517467 := by
  cases C with
  | zero => simp [program, measurementCount]
  | @some cx cy hc =>
    have h := (finiteProgramN_counts layout layout_widths (.some hc) cy
      (fastGeneric2 layout cx cy) hc rfl).2
    have g := (fastGeneric2_counts layout layout_widths cx cy).2
    change measurementCount (finiteProgramN layout (.some hc) cy (fastGeneric2 layout cx cy)) ≤ _
    omega

theorem io_subset_sitesR : ioWires ⊆ sitesR layout := by
  intro w hw
  rcases io_partition w hw with hp|hc
  · exact point_R layout layout_widths layout_nodup w hp
  · rw [hc]; exact control_R layout layout_widths layout_nodup

/-- The static inventory excludes the proved idle pool site 1804. -/
theorem program_qubits (C : Point) : qubits (program C) ≤ 1891 := by
  cases C with
  | zero =>
    change qubits [] ≤ 1891
    rw [qubits_empty]
    decide
  | @some cx cy hc =>
    have support := finiteProgramN_supportR layout layout_widths layout_nodup (.some hc) cy _
      (fastGenericG layout layout_widths layout_nodup cx cy)
      (fastGeneric2_no_pool1804 layout layout_widths layout_nodup cx cy)
    have card := Finset.card_le_card (Finset.union_subset io_subset_sitesR support)
    exact card.trans (sitesR_card layout layout_widths layout_nodup)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program, GatePhysical]
  | @some cx cy hc =>
    exact finiteProgramN_physical layout layout_widths layout_nodup _ cy _
      (fastGeneric2_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C) ≤ 47000000 := by
  cases C with
  | zero => simp [program, gateSlots]
  | @some cx cy hc =>
    have h := finiteProgramN_gateSlots layout layout_widths (.some hc) cy
      (fastGeneric2 layout cx cy)
    have g := fastGeneric2_gateSlots_le layout layout_widths cx cy
    change gateSlots (finiteProgramN layout (.some hc) cy (fastGeneric2 layout cx cy)) ≤ _
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C)) ≤ 1517467
    rw [normalize_measurements]
    exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C)) ≤ 1891
    rw [normalize_qubits]
    exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C)) ≤ 47000000
    rw [normalize_slots]
    exact program_gateSlots C

end ECDSAAdd.Entrant
