import ECDSAAdd.Submission.Entrant.FrontierEntry1591Kernel
import ECDSAAdd.Submission.Entrant.FrontierEntry1591Point

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Entrant.OwnParity1591Actual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite FrontierEntry1591Kernel

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  FrontierEntry1591Point.gen entryKernel exitKernel L cx cy

theorem sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  FrontierEntry1591Point.sites entryKernel exitKernel entry_support exit_support L hw hn cx cy

theorem ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) :=
  FrontierEntry1591Point.ok entryKernel exitKernel entry_support exit_support
    entry_correct exit_correct L hw hn hc

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    GatePhysical (gen L cx cy) :=
  FrontierEntry1591Point.physical entryKernel exitKernel entry_support exit_support
    entry_physical exit_physical L hw hn cx cy

theorem counts_eq (L : ControlledPointLayout) (cx cy : Fp) :
    toffoliCount (gen L cx cy)=toffoliCount (OwnOneFlagActual.gen L cx cy) ∧
      measurementCount (gen L cx cy)=measurementCount (OwnOneFlagActual.gen L cx cy) :=
  FrontierEntry1591Point.counts_eq entryKernel exitKernel entry_counts_eq exit_counts_eq L cx cy

theorem slots (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (gen L cx cy)≤49204896 :=
  FrontierEntry1591Point.slots entryKernel exitKernel entry_slots exit_slots L hw cx cy

theorem qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1591 :=
  FrontierEntry1591Point.qubits entryKernel exitKernel entry_support exit_support
    entry_free exit_free C cx cy

end ECDSAAdd.Entrant.OwnParity1591Actual
