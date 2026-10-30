import ECDSAAdd.Submission.Entrant.FrontierEntryJoint1591Correct
import ECDSAAdd.Submission.Entrant.FrontierEntryJoint1591PointResources

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntryJoint1591Final
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

private theorem gen_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (FrontierEntryJoint1591.gen L cx cy) :=
  FrontierEntry1591Point.ok FrontierEntryJoint1591.entryKernel FrontierEntry1591Kernel.exitKernel
    FrontierEntryJoint1591.entryKernel_support FrontierEntry1591Kernel.exit_support
    FrontierEntryJoint1591.entry_correct FrontierEntry1591Kernel.exit_correct L hw hn hc

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (FrontierEntryJoint1591.gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2154141,1500105,1591,50004900⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have hG := FrontierEntryJoint1591.gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (gen_ok layout layout_widths layout_nodup hc) hG)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ hG).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2154141 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    exact FrontierEntryJoint1591.wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C)≤1500105 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    exact FrontierEntryJoint1591.wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C)≤1591 := by
  cases C with
  | zero => change qubits []≤1591;rw [qubits_empty];decide
  | @some cx cy hc =>
    exact FrontierEntryJoint1591.wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact FrontierEntryJoint1591.wrapper_physical (.some hc) cx cy

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50004900 := by
  cases C with
  | zero => simp [program,gateSlots]
  | @some cx cy hc =>
    exact FrontierEntryJoint1591.wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1500105
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1591
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50004900
    rw [normalize_slots];exact program_gateSlots C

end ECDSAAdd.Entrant.FrontierEntryJoint1591Final
