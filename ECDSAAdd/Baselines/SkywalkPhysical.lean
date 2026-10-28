import ECDSAAdd.Arithmetic.SkywalkPointPhysical
import ECDSAAdd.Baselines.NormalizedEntries
namespace ECDSAAdd.Baselines
open Arithmetic Secp256k1
attribute [local irreducible] pointCompressedDialogFinite

theorem skywalk_physical (C : Point) : GatePhysical (skywalk C) := by
  cases C with
  | zero => simp [skywalk,Submissions.Skywalk.program,controlledPointAdd,GatePhysical]
  | some hc => exact skywalkFinite_physical layout layout_widths layout_nodup _ _ _

theorem normalizedSkywalk_physical (C : Point) :
    ∀ i ∈ normalizedSkywalk C, Challenge.instructionValid i :=
  normalize_physical _ (skywalk_physical C)
end ECDSAAdd.Baselines
