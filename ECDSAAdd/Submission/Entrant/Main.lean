import ECDSAAdd.Submission.Entrant.OneFlag
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (OwnOneFlagActual.gen layout cx cy)
def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2154595,1500576,1592,50000004⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have cfg:=MappedCompressed.LaneA.laneLogical_config
    have above:History5.HistoryAbove MappedCompressed.base:=by intro j hj;simp [MappedCompressed.base]
    have hG:=OwnOneFlagActual.sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (OwnOneFlagActual.ok layout layout_widths layout_nodup cfg.1 above cfg.2.1 cfg.2.2 hc) hG)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ hG).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2154595 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc =>
    have h:=(Edges.wrapper_counts layout layout_widths (OwnOneFlagActual.gen layout cx cy) hc).1
    have g:=(SelGeneric5.program_counts layout layout_widths cx cy).1
    have gf:=(genF_counts layout layout_widths cx cy).1
    have gd:=(genFFused_counts_diff layout layout_widths cx cy).1
    have ge:=(OwnExitProducer.genE_counts_diff layout layout_widths cx cy).1
    have gq:=(OwnQ6Producer.genE_counts_eq layout cx cy).1
    have gn:=(OwnOneFlagActual.counts_eq layout layout_widths cx cy).1
    have ga:=(OwnDiagEndpointActual.genE_counts_diff layout layout_widths cx cy).1
    change toffoliCount (Edges.wrapper layout (.some hc) cy (OwnOneFlagActual.gen layout cx cy))≤2154595
    omega

theorem program_measurements (C : Point) : measurementCount (program C)≤1500576 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc =>
    have h:=(Edges.wrapper_counts layout layout_widths (OwnOneFlagActual.gen layout cx cy) hc).2
    have g:=(SelGeneric5.program_counts layout layout_widths cx cy).2
    have gf:=(genF_counts layout layout_widths cx cy).2
    have gd:=(genFFused_counts_diff layout layout_widths cx cy).2
    have ge:=(OwnExitProducer.genE_counts_diff layout layout_widths cx cy).2
    have gq:=(OwnQ6Producer.genE_counts_eq layout cx cy).2
    have gn:=(OwnOneFlagActual.counts_eq layout layout_widths cx cy).2
    have ga:=(OwnDiagEndpointActual.genE_counts_diff layout layout_widths cx cy).2
    change measurementCount (Edges.wrapper layout (.some hc) cy (OwnOneFlagActual.gen layout cx cy))≤1500576
    omega

theorem program_qubits (C : Point) : qubits (program C)≤1592 := by
  cases C with
  | zero => change qubits []≤1592;rw [qubits_empty];decide
  | @some cx cy hc => exact OwnOneFlagActual.qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (OwnOneFlagActual.physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50000004 := by
  cases C with
  | zero => simp [program,gateSlots]
  | @some cx cy hc =>
    have h:=Edges.wrapper_slots layout layout_widths (.some hc) cy (OwnOneFlagActual.gen layout cx cy)
    have g:=OwnOneFlagActual.slots layout layout_widths cx cy
    change gateSlots (Edges.wrapper layout (.some hc) cy (OwnOneFlagActual.gen layout cx cy))≤_
    omega

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1500576
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1592
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50000004
    rw [normalize_slots];exact program_gateSlots C
end ECDSAAdd.Entrant

