import ECDSAAdd.Submission.Entrant.MainPart07

namespace ECDSAAdd.Entrant.WireWitness
open ECDSAAdd Arithmetic
attribute [local irreducible] wires

def atWire (P : Program) (q k : Nat) : Bool :=
  match P[k]? with
  | none => false
  | some instruction => decide (q∈instruction.wires)

theorem of_member (P : Program) (q : Wire) (instruction : Instr) (member : instruction∈P)
    (used : q∈instruction.wires) : q∈wires P := by
  induction P with
  | nil => simp at member
  | cons head tail ih =>
    rw [wires]
    rcases List.mem_cons.mp member with equal|member
    · subst head; exact Finset.mem_union_left _ used
    · exact Finset.mem_union_right _ (ih member)

theorem atWire_sound (P : Program) (q k : Nat) (checked : atWire P q k=true) : q∈wires P := by
  cases found : P[k]? with
  | none => simp only [atWire,found,Bool.false_eq_true] at checked
  | some instruction =>
    have used : q∈instruction.wires := by simpa only [atWire,found,decide_eq_true_eq] using checked
    exact of_member P q instruction (List.mem_of_getElem? found) used

end ECDSAAdd.Entrant.WireWitness
