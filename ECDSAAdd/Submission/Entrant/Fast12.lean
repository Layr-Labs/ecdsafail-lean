import ECDSAAdd.Submission.Entrant.Fast11
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
namespace ECDSAAdd.Entrant.ZeroFill
open Arithmetic

theorem correctionWires_length_research (a : Nat) (ts : List (Nat × Wire × Wire)) :
    (correctionWires a ts).length ≤ 2 * ts.length := by
  induction ts with
  | nil => simp [correctionWires]
  | cons x xs ih =>
    obtain ⟨i,p,c⟩ := x
    cases hb : a.testBit i <;> simp [correctionWires, hb] at ih ⊢ <;> omega

theorem compareCorrections_length_research (bit : Bool) (x v e : Wire) (ws : List Wire) :
    (compareCorrections bit x v e ws).length ≤ 3 + ws.length := by
  cases bit <;> simp [compareCorrections] <;> omega

theorem clearFV_slots_research (a : Nat) (aL aH : Bool) (U V F xlo xhi el eh : Wire)
    (top mid : List (Nat × Wire × Wire)) :
    Challenge.gateSlots (clearFV a aL aH U V F xlo xhi el eh top mid) ≤ 8 + 2 * (top.length + mid.length) := by
  have ht := correctionWires_length_research a top
  have hm := correctionWires_length_research a mid
  have hc1 := compareCorrections_length_research aH xhi V eh (correctionWires a top)
  have hc2 := compareCorrections_length_research aL xlo U el (correctionWires a mid)
  simp only [clearFV, Challenge.gateSlots, Challenge.instructionSlots, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_nil, Nat.add_zero]
  omega

theorem finishUOne_slots_research (a : Nat) (one U : Wire) (low : List (Nat × Wire × Wire)) :
    Challenge.gateSlots (finishUOne a one U low) ≤ 2 * low.length + 1 := by
  have h := xorAcc_slots a U low
  unfold finishUOne
  rw [Challenge.gateSlots_append]
  have hx : Challenge.gateSlots [.X one] = 1 := rfl
  rw [hx]
  omega

theorem fastExtract_slots_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh g pk : Wire)
    (top mid low : List (Nat × Wire × Wire)) :
    Challenge.gateSlots (fastExtract a aL aH one U V F xlo xhi el eh g pk top mid low) ≤
      4 * (top.length + mid.length + low.length) + 19 := by
  have hp := (pre_counts a aL aH one U V F xlo xhi el eh top mid low).2.2
  have hc := clearFV_slots_research a aL aH U V F xlo xhi el eh top mid
  have hf := finishUOne_slots_research a one U low
  unfold fastExtract
  simp only [Challenge.gateSlots_append]
  have hcc : Challenge.gateSlots [.CCX g F pk] = 1 := rfl
  rw [hcc]
  omega
end ECDSAAdd.Entrant.ZeroFill
