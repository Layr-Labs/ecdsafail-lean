import ECDSAAdd.Submission.Entrant.FrontierEntry1592Generic
import ECDSAAdd.Submission.Entrant.FrontierEntry1592Division

/-! Final entry callback instantiation. All unchanged components are the
accepted 682a30a9 OneFlag source; the new callback supplies every required proof. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1592Final
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite

def division : Fp → Program := FrontierEntry1592Division.fusedDivisionF layout

private theorem division_correct :
    ∀ (X Y k : Fp) (G : Bool) (origin : BasisState), X ≠ 0 →
      Triple (PointDialogValues layout X Y G origin) (division k)
        (PointDialogValues layout X ((Y + (if G then k else 0)) / X) G origin) := by
  have cfg := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove MappedCompressed.base := by
    intro j hj
    simp [MappedCompressed.base]
  exact FrontierEntry1592Division.fusedDivisionF_step OwnQ6Actual.entry_selected_free
    layout layout_widths layout_nodup cfg.1 above cfg.2.1 cfg.2.2

private theorem division_support (k : Fp) :
    wires (division k) ⊆ (OB5Support.sites layout).toFinset :=
  FrontierEntry1592Division.fusedDivisionF_support layout layout_widths layout_nodup k

private theorem division_counts (k : Fp) :
    toffoliCount (division k) + 505 = toffoliCount (OwnOneFlagEntryQ7.fusedDivisionF layout k) ∧
    measurementCount (division k) + 509 = measurementCount (OwnOneFlagEntryQ7.fusedDivisionF layout k) :=
  FrontierEntry1592Division.fusedDivisionF_counts_diff layout layout_widths layout_nodup k

private theorem division_physical (k : Fp) : GatePhysical (division k) :=
  FrontierEntry1592Division.fusedDivisionF_physical layout layout_widths layout_nodup k

private theorem division_free (k : Nat) (hk : k ∈ ([1800,766,765,767,770,1285,1286] : List Nat))
    (c : Fp) : layout.core.poolWire k ∉ wires (division c) :=
  FrontierEntry1592Division.fusedDivisionF_free layout layout_widths layout_nodup
    OwnQ6Actual.entry_selected_free k hk c

private theorem division_slots (k : Fp) : gateSlots (division k) ≤ 20525006 :=
  FrontierEntry1592Division.fusedDivisionF_slots_le layout layout_widths layout_nodup k

def program := FrontierEntry1592Certificate.program division
def entry := FrontierEntry1592Certificate.entry division
def bounds := FrontierEntry1592Certificate.bounds

theorem certificate : Challenge.Certificate entry bounds :=
  FrontierEntry1592Certificate.certificate division division_correct division_support
    division_counts division_physical division_free division_slots
end ECDSAAdd.Entrant.FrontierEntry1592Final

namespace ECDSAAdd.Entrant
def program := FrontierEntry1592Final.program
def entry := FrontierEntry1592Final.entry
def bounds := FrontierEntry1592Final.bounds
theorem certificate : Challenge.Certificate entry bounds := FrontierEntry1592Final.certificate
end ECDSAAdd.Entrant
