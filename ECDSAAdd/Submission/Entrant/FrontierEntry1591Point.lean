import ECDSAAdd.Submission.Entrant.FrontierEntry1591CallerResources
import ECDSAAdd.Submission.Entrant.PrefixFrontierSquare1591

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591Point
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite FrontierEntry1591Callers
attribute [local irreducible] wires run toffoliCount measurementCount

def gen (K E : Program) (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  All12Generic.gen L (division K L) (PrefixFrontierSquare1591.program L) (exit E L) cx cy

theorem square_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (PrefixFrontierSquare1591.program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (2^163-1:Nat) else 0)) Y G origin) := by
  have h := PrefixFrontierSquare1591.correct L hw hn X Y G origin
  cases G <;> simpa only [OwnDiagAll12Square.cFlipK,Bool.false_eq_true,if_false,if_true,Nat.cast_zero] using h

theorem ok (K E : Program) (ks : wires K⊆OB5Support.logicalSites)
    (es : wires E⊆OB5Support.logicalSites) (kc : EntryCorrect K) (ec : ExitCorrect E)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen K E L cx cy) := by
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  exact All12Generic.genFFused_ok L hw hn _ _ _ (exit_correct E es ec L hw hn)
    (division_step K ks kc L hw hn config.1 above config.2.1 config.2.2)
    (square_step L hw hn) hc

theorem sites (K E : Program) (ks : wires K⊆OB5Support.logicalSites)
    (es : wires E⊆OB5Support.logicalSites) (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (gen K E L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  Q1591Resources.gen_sites L hw hn _ _ _ (division_support K ks L hw)
    (PrefixFrontierSquare1591.support L hw hn) (exit_support E es L hw) cx cy

theorem physical (K E : Program) (ks : wires K⊆OB5Support.logicalSites)
    (es : wires E⊆OB5Support.logicalSites) (kp : GatePhysical K) (ep : GatePhysical E)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    GatePhysical (gen K E L cx cy) :=
  Q1591Resources.gen_physical L hw hn _ _ _ (division_physical K ks kp L hw hn)
    (PrefixFrontierSquare1591.physical L hw hn) (placed_physical E es ep L hw hn) cx cy

theorem counts_eq (K E : Program)
    (kc : toffoliCount K=toffoliCount OwnOneFlagEntryQ7.kernel5S ∧
      measurementCount K=measurementCount OwnOneFlagEntryQ7.kernel5S)
    (ec : toffoliCount E=toffoliCount OwnOneFlagExitQ7.kernelS ∧
      measurementCount E=measurementCount OwnOneFlagExitQ7.kernelS)
    (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (gen K E L cx cy)=toffoliCount (OwnOneFlagActual.gen L cx cy) ∧
      measurementCount (gen K E L cx cy)=measurementCount (OwnOneFlagActual.gen L cx cy) :=
  Q1591Resources.gen_counts_eq L _ _ _ (division_counts_eq K kc L)
    (PrefixFrontierSquare1591.counts L) (exit_counts_eq E ec L) cx cy

theorem slots (K E : Program) (ks : gateSlots K≤20502454) (es : gateSlots E≤20502454)
    (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (gen K E L cx cy)≤49204896 :=
  Q1591Resources.gen_slots L hw _ _ _ (division_slots K ks L hw)
    (PrefixFrontierSquare1591.slots L hw) (exit_slots E es L) cx cy

theorem qubits (K E : Program) (ks : wires K⊆OB5Support.logicalSites)
    (es : wires E⊆OB5Support.logicalSites)
    (kf : ∀i∈logicalOmissions,base i∉wires K)
    (ef : ∀i∈logicalOmissions,base i∉wires E) (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen K E layout cx cy))≤1591 :=
  Q1591Resources.gen_qubits _ _ _ (division_support K ks layout layout_widths)
    (PrefixFrontierSquare1591.support layout layout_widths layout_nodup)
    (exit_support E es layout layout_widths)
    (division_free K ks kf layout layout_widths layout_nodup)
    (PrefixFrontierSquare1591.square_free layout layout_widths layout_nodup)
    (placed_omissions E es ef layout layout_widths layout_nodup) C cx cy

end ECDSAAdd.Entrant.FrontierEntry1591Point
