import ECDSAAdd.Submission.Entrant.FrontierEntryGeneric
import ECDSAAdd.Submission.Entrant.FrontierEntryDivision

/-! Final entry callback instantiation. All unchanged components are the
accepted 4c326f52 source; the new callback supplies every required proof. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntryFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite

def division : Fp → Program := FrontierEntryDivision.fusedDivisionF layout

private theorem division_correct :
    ∀ (X Y k : Fp) (G : Bool) (origin : BasisState), X ≠ 0 →
      Triple (PointDialogValues layout X Y G origin) (division k)
        (PointDialogValues layout X ((Y + (if G then k else 0)) / X) G origin) := by
  have cfg := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove MappedCompressed.base := by
    intro j hj
    simp [MappedCompressed.base]
  exact FrontierEntryDivision.fusedDivisionF_step OwnQ6Actual.entry_selected_free
    layout layout_widths layout_nodup cfg.1 above cfg.2.1 cfg.2.2

private theorem division_support (k : Fp) :
    wires (division k) ⊆ (OB5Support.sites layout).toFinset :=
  FrontierEntryDivision.fusedDivisionF_support layout layout_widths layout_nodup k

private theorem division_counts (k : Fp) :
    toffoliCount (division k) + 251 = toffoliCount (OwnEndpointEntryQ6.fusedDivisionF layout k) ∧
    measurementCount (division k) + 509 = measurementCount (OwnEndpointEntryQ6.fusedDivisionF layout k) := by
  have fresh := FrontierEntryDivision.fusedDivisionF_counts_diff layout layout_widths layout_nodup k
  have endpoint := EndpointEntryProperties.division_counts_diff _
    (EndpointNormalParent.division_counts OwnEntryFuseQ5.kernel5_counts layout layout_widths k)
    layout layout_widths k
  constructor <;> omega

private theorem division_physical (k : Fp) : GatePhysical (division k) :=
  FrontierEntryDivision.fusedDivisionF_physical layout layout_widths layout_nodup k

private theorem division_free (k : Nat) (hk : k ∈ ([1800,766,765,767,770,1285] : List Nat))
    (c : Fp) : layout.core.poolWire k ∉ wires (division c) :=
  FrontierEntryDivision.fusedDivisionF_free layout layout_widths layout_nodup
    OwnQ6Actual.entry_selected_free k hk c

private theorem division_slots (k : Fp) : gateSlots (division k) ≤ 20525006 :=
  (FrontierEntryDivision.fusedDivisionF_slots_le layout layout_widths layout_nodup k).trans
    (All12Generic.actual_division_slots layout layout_widths k)

def program := FrontierEntryCertificate.program division
def entry := FrontierEntryCertificate.entry division
def bounds := FrontierEntryCertificate.bounds

theorem certificate : Challenge.Certificate entry bounds :=
  FrontierEntryCertificate.certificate division division_correct division_support
    division_counts division_physical division_free division_slots
end ECDSAAdd.Entrant.FrontierEntryFinal

namespace ECDSAAdd.Entrant
def program := FrontierEntryFinal.program
def entry := FrontierEntryFinal.entry
def bounds := FrontierEntryFinal.bounds
theorem certificate : Challenge.Certificate entry bounds := FrontierEntryFinal.certificate
end ECDSAAdd.Entrant
