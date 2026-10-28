import ECDSAAdd.Challenge.Contract

namespace ECDSAAdd.Challenge.Regression
open Secp256k1

private theorem regValue_zero (r : List Wire) : regValue r (fun _ => false) = 0 := by
  induction r with
  | nil => rfl
  | cons w r ih =>
    change 0 + 2 * regValue r (fun _ => false) = 0
    rw [ih]

private theorem zero_encoded : encodes false (0 : Point) (fun _ => false) := by
  refine ⟨rfl, ?_, fun _ _ => rfl⟩
  change false = false ∧ regValue point.x (fun _ => false) = 0 ∧
    regValue point.y (fun _ => false) = 0
  exact ⟨rfl, regValue_zero _, regValue_zero _⟩

/-- A wire omitted from an entrant-chosen work list is still protected. -/
theorem dirty_wire_rejected :
    ¬ Triple (encodes false (0 : Point)) [.X 514] (encodes false 0) := by
  intro h
  have hz := (h ⟨false, fun _ => false⟩ [] zero_encoded).2.2.2 514 (by decide)
  simp [run, writeBit] at hz

/-- Basis restoration alone is insufficient; measurement phase must cancel. -/
theorem phase_debt_rejected :
    ¬ Triple (encodes false (0 : Point)) [.X 514, .measureX 514 [] []]
      (encodes false 0) := by
  intro h
  have hp := (h ⟨false, fun _ => false⟩ [true] zero_encoded).1
  simp [run, measureAndCorrect, correct, writeBit] at hp

theorem aliased_cx_rejected : ¬ instructionValid (.CX 0 0) := by
  simp [instructionValid]

theorem aliased_ccx_rejected : ¬ instructionValid (.CCX 0 0 1) := by
  simp [instructionValid]

theorem both_correction_branches_counted :
    gateSlots [.measureX 0 [.Z 1] [.Z 2, .CZ 3 4]] = 4 := rfl

end ECDSAAdd.Challenge.Regression
