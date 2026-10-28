import ECDSAAdd.Arithmetic.ValueWalkPointPhysical
import ECDSAAdd.Baselines.NormalizedEntries
namespace ECDSAAdd.Baselines
open Arithmetic Secp256k1
attribute [local irreducible] valueWalkPointDialogFinite

theorem valueWalk_physical (C : Point) : GatePhysical (valueWalk C) := by
  cases C with
  | zero => simp [valueWalk,Submissions.ValueWalk.program,GatePhysical]
  | some hc => exact valueWalkFinite_physical layout layout_widths layout_nodup _ _ _

theorem normalizedValueWalk_physical (C : Point) :
    ∀ i ∈ normalizedValueWalk C, Challenge.instructionValid i :=
  normalize_physical _ (valueWalk_physical C)
end ECDSAAdd.Baselines
