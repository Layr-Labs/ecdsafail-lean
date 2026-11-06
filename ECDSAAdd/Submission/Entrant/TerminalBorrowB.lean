import ECDSAAdd.Submission.Entrant.MainPart07

namespace ECDSAAdd.Entrant.TerminalBorrowB
open ECDSAAdd Arithmetic MappedCompressed History5 OB5
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires Rolling1588.reverse Rolling1588.Integer.reverse

def sites : List Wire := List.range' 793 13

theorem first_prefix : sites.toFinset ⊆ wires ((W.ReverseCarry.compactReceiverTick base 1).take 24) := by
  decide +kernel

theorem take_subset (P : Program) (n : Nat) : wires (P.take n)⊆wires P := by
  have sub : wires (P.take n)⊆wires (P.take n++P.drop n) := by
    rw [wires_append]
    exact Finset.subset_union_left
  simpa only [List.take_append_drop] using sub

theorem first_sites : sites.toFinset ⊆ wires (W.ReverseCarry.compactReceiverTick base 1) :=
  first_prefix.trans (take_subset _ 24)

theorem sig_fixed : ∀q∈sites, sig 1 q=q := by decide +kernel

theorem unpack1 (isA : Bool) : Rolling1588.Integer.unpackFirst base isA 1=[] := by
  simp only [Rolling1588.Integer.unpackFirst,show ¬(1:Nat)=5 from by decide,if_false,
    Rolling1588.Integer.decodeBefore,show History5.packDue 1=false from by decide,
    Bool.false_eq_true,if_false]

theorem reverse_sites (isA : Bool) : sites.toFinset ⊆ wires (Rolling1588.reverse isA 1 505) := by
  intro q hq
  have member : q∈wires (renameProgram (sig 1) (W.ReverseCarry.compactReceiverTick base 1)) := by
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨q,first_sites hq,sig_fixed q (List.mem_toFinset.mp hq)⟩
  rw [←Rolling1588.Integer.reverse_eq_packets,Rolling1588.Integer.reverse,wires_append]
  apply Finset.mem_union_right
  simpa only [unpack1,List.nil_append] using member

end ECDSAAdd.Entrant.TerminalBorrowB
