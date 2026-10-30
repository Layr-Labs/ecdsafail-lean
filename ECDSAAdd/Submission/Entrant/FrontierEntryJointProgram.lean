import ECDSAAdd.Submission.Entrant.FrontierEntryFrame
import ECDSAAdd.Submission.Entrant.FrontierEntryResources

set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FrontierEntry
open Arithmetic BalancedCircuit BalancedField

def joint (L : BalancedCircuit.Layout) (J G : Wire) : Program :=
  [.X G] ++ EntryRetained5.program L J G ++ [.X G]


theorem joint_counts (L : BalancedCircuit.Layout) (hw : L.Widths) (J G : Wire) :
    toffoliCount (joint L J G) = 771 ∧ measurementCount (joint L J G) = 514 := by
  have h := EntryRetained5.counts L hw J G
  have tx : toffoliCount [Instr.X G] = 0 := rfl
  have mx : measurementCount [Instr.X G] = 0 := rfl
  simpa only [joint, toffoliCount_append, measurementCount_append,
    tx, mx, Nat.zero_add, Nat.add_zero] using h

theorem joint_slots_le (L : BalancedCircuit.Layout) (hw : L.Widths) (J G : Wire) :
    Challenge.gateSlots (joint L J G) ≤ 8002 := by
  have h := EntryRetained5.program_slots_le L hw J G
  have x : Challenge.gateSlots [Instr.X G] = 1 := rfl
  simp only [joint, Challenge.gateSlots_append, x]
  omega

end ECDSAAdd.Entrant.FrontierEntry
