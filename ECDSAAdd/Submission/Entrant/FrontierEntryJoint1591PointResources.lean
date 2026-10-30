import ECDSAAdd.Submission.Entrant.FrontierEntryJoint1591Resources
import ECDSAAdd.Submission.Entrant.FrontierEntry1591Actual

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntryJoint1591
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run toffoliCount measurementCount gateSlots

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  FrontierEntry1591Point.gen entryKernel FrontierEntry1591Kernel.exitKernel L cx cy

theorem division_counts_diff (L : ControlledPointLayout) (k : Fp) :
    toffoliCount (FrontierEntry1591Callers.division entryKernel L k)+505=
      toffoliCount (FrontierEntry1591Callers.division FrontierEntry1591Kernel.entryKernel L k) ∧
    measurementCount (FrontierEntry1591Callers.division entryKernel L k)+509=
      measurementCount (FrontierEntry1591Callers.division FrontierEntry1591Kernel.entryKernel L k) := by
  have diff:=entryKernel_counts_diff
  simp only [FrontierEntry1591Callers.division,FrontierEntry1591Callers.entry,
    toffoliCount_append,measurementCount_append,renameProgram_counts]
  exact ⟨by omega,by omega⟩

theorem gen_counts_diff (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+505=toffoliCount (OwnParity1591Actual.gen L cx cy) ∧
    measurementCount (gen L cx cy)+509=measurementCount (OwnParity1591Actual.gen L cx cy) := by
  have diff:=division_counts_diff L (-cy)
  simp only [gen,OwnParity1591Actual.gen,FrontierEntry1591Point.gen,
    All12Generic.gen,All12Generic.mid,All12Generic.generic,
    toffoliCount_append,measurementCount_append,renameProgram_counts]
  exact ⟨by omega,by omega⟩

theorem gen_counts_diff_oneflag (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+505=toffoliCount (OwnOneFlagActual.gen L cx cy) ∧
    measurementCount (gen L cx cy)+509=measurementCount (OwnOneFlagActual.gen L cx cy) :=
  ⟨(gen_counts_diff L cx cy).1.trans (OwnParity1591Actual.counts_eq L cx cy).1,
    (gen_counts_diff L cx cy).2.trans (OwnParity1591Actual.counts_eq L cx cy).2⟩

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  FrontierEntry1591Point.sites entryKernel FrontierEntry1591Kernel.exitKernel
    entryKernel_support FrontierEntry1591Kernel.exit_support L hw hn cx cy

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) :=
  FrontierEntry1591Point.physical entryKernel FrontierEntry1591Kernel.exitKernel
    entryKernel_support FrontierEntry1591Kernel.exit_support
    entryKernel_physical FrontierEntry1591Kernel.exit_physical L hw hn cx cy

theorem gen_slots (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (gen L cx cy)≤49204896 :=
  FrontierEntry1591Point.slots entryKernel FrontierEntry1591Kernel.exitKernel
    entryKernel_slots FrontierEntry1591Kernel.exit_slots L hw cx cy

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1591 :=
  FrontierEntry1591Point.qubits entryKernel FrontierEntry1591Kernel.exitKernel
    entryKernel_support FrontierEntry1591Kernel.exit_support
    entryKernel_free FrontierEntry1591Kernel.exit_free C cx cy

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50004900 :=
  Q1591Resources.wrapper_slots layout layout_widths _ (gen_slots layout layout_widths cx cy) C cy

theorem wrapper_physical (C : Point) (cx cy : Fp) :
    GatePhysical (Edges.wrapper layout C cy (gen layout cx cy)) :=
  Edges.wrapper_physical layout layout_widths layout_nodup C cy _
    (gen_physical layout layout_widths layout_nodup cx cy)

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2154141 := by
  have h:=(Edges.wrapper_counts layout layout_widths (gen layout cx cy) hc).1
  have g:=(SelGeneric5.program_counts layout layout_widths cx cy).1
  have gf:=(genF_counts layout layout_widths cx cy).1
  have gd:=(genFFused_counts_diff layout layout_widths cx cy).1
  have ge:=(OwnExitProducer.genE_counts_diff layout layout_widths cx cy).1
  have gq:=(OwnQ6Producer.genE_counts_eq layout cx cy).1
  have gc:=(gen_counts_diff_oneflag layout cx cy).1
  have gn:=(OwnOneFlagActual.counts_eq layout layout_widths cx cy).1
  have ga:=(OwnDiagEndpointActual.genE_counts_diff layout layout_widths cx cy).1
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1500105 := by
  have h:=(Edges.wrapper_counts layout layout_widths (gen layout cx cy) hc).2
  have g:=(SelGeneric5.program_counts layout layout_widths cx cy).2
  have gf:=(genF_counts layout layout_widths cx cy).2
  have gd:=(genFFused_counts_diff layout layout_widths cx cy).2
  have ge:=(OwnExitProducer.genE_counts_diff layout layout_widths cx cy).2
  have gq:=(OwnQ6Producer.genE_counts_eq layout cx cy).2
  have gc:=(gen_counts_diff_oneflag layout cx cy).2
  have gn:=(OwnOneFlagActual.counts_eq layout layout_widths cx cy).2
  have ga:=(OwnDiagEndpointActual.genE_counts_diff layout layout_widths cx cy).2
  omega

end ECDSAAdd.Entrant.FrontierEntryJoint1591
