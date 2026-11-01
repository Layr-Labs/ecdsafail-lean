import ECDSAAdd.Submission.Entrant.MainC
import ECDSAAdd.Submission.Entrant.FusedFlags

namespace ECDSAAdd.Entrant.FusedBoundaryFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      FusedFlags.wrapper layout C cy (FiniteFlagInterval.gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2152555,1499138,1588,50167449⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites := FiniteFlagInterval.gen_sites layout layout_widths layout_nodup cx cy
    have support := (FusedFlags.wrapper_support layout hc (FiniteFlagInterval.gen layout cx cy)).trans
      (Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites)
    exact fixed_correct _ b R _
      (FusedFlags.full_spec layout layout_widths layout_nodup R hc b _
        (FiniteFlagInterval.genFFused_ok layout layout_widths layout_nodup hc) sites)
      (support.trans (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2152555 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).1
    have old := FiniteFlagInterval.wrapper_toffoli cx cy hc
    change toffoliCount (FusedFlags.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤2152555
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1499138 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.1
    have old := FiniteFlagInterval.wrapper_measurements cx cy hc
    change measurementCount (FusedFlags.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤1499138
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1588 := by
  cases C with
  | zero => change qubits []≤1588; rw [qubits_empty]; decide
  | @some cx cy hc =>
    have h := FusedFlags.wrapper_support layout hc (FiniteFlagInterval.gen layout cx cy)
    exact (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl ioWires) h)).trans
      (FiniteFlagInterval.wrapper_qubits (.some hc) cx cy)

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact FusedFlags.wrapper_physical layout layout_widths layout_nodup _ cy _
      (FiniteFlagInterval.gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50167449 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    have f := (FusedFlags.wrapper_counts layout (FiniteFlagInterval.gen layout cx cy) hc).2.2
    have old := FiniteFlagInterval.wrapper_slots (.some hc) cx cy
    change gateSlots (FusedFlags.wrapper layout (.some hc) cy (FiniteFlagInterval.gen layout cx cy))≤50167449
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1499138
    rw [normalize_measurements]; exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1588
    rw [normalize_qubits]; exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50167449
    rw [normalize_slots]; exact program_gateSlots C

end ECDSAAdd.Entrant.FusedBoundaryFinal
