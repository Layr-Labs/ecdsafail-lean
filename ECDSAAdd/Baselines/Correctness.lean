import ECDSAAdd.Baselines.Frame

namespace ECDSAAdd.Baselines
open Arithmetic Secp256k1
attribute [local irreducible] valueWalkPointDialogFinite wires

def skywalk : Challenge.Entry := Submissions.Skywalk.program layout
def valueWalk : Challenge.Entry := Submissions.ValueWalk.program layout

theorem skywalk_correct (C : Point) (b : Bool) (R : Point) :
    Triple (Challenge.encodes b R) (skywalk C)
      (Challenge.encodes b (if b then R+C else R)) := by
  apply fixed_correct _ b R _ (Submissions.Skywalk.correctness layout layout_widths layout_nodup b R C)
  cases C with
  | zero => simp [Submissions.Skywalk.program, controlledPointAdd, wires]
  | some hc => exact CompressedPointDialog.finite_wires layout layout_widths layout_nodup _ _ _

theorem valueWalk_correct (C : Point) (b : Bool) (R : Point) :
    Triple (Challenge.encodes b R) (valueWalk C)
      (Challenge.encodes b (if b then R+C else R)) := by
  apply fixed_correct _ b R _ (Submissions.ValueWalk.correctness layout layout_widths layout_nodup b R C)
  cases C with
  | zero => simp [Submissions.ValueWalk.program, wires]
  | some hc =>
    exact (valueWalkPointDialogFinite_wires layout layout_widths layout_nodup _ _ _).le

theorem skywalk_toffoli (C : Point) : toffoliCount (skywalk C) ≤ 2217386 := by
  cases C with
  | zero => simp [skywalk, Submissions.Skywalk.program, controlledPointAdd, toffoliCount]
  | some hc => exact (Submissions.Skywalk.gate_count layout layout_widths layout_nodup _ _ hc).le

theorem skywalk_measurements (C : Point) : measurementCount (skywalk C) ≤ 1557928 := by
  cases C with
  | zero => simp [skywalk, Submissions.Skywalk.program, controlledPointAdd, measurementCount]
  | some hc => exact (Submissions.Skywalk.measurement_count layout layout_widths layout_nodup _ _ hc).le

theorem valueWalk_toffoli (C : Point) : toffoliCount (valueWalk C) ≤ 6286806 := by
  cases C with
  | zero => simp [valueWalk, Submissions.ValueWalk.program, toffoliCount]
  | some hc => exact (Submissions.ValueWalk.gate_count layout layout_widths layout_nodup _ _ hc).le

theorem valueWalk_measurements (C : Point) : measurementCount (valueWalk C) ≤ 3779274 := by
  cases C with
  | zero => simp [valueWalk, Submissions.ValueWalk.program, measurementCount]
  | some hc => exact (Submissions.ValueWalk.measurement_count layout layout_widths layout_nodup _ _ hc).le

end ECDSAAdd.Baselines
