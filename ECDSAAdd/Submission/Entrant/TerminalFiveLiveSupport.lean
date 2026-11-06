import ECDSAAdd.Submission.Entrant.TerminalFiveBridge
import ECDSAAdd.Submission.Entrant.TerminalBorrowB
import ECDSAAdd.Submission.Entrant.WireWitness

namespace ECDSAAdd.Entrant.TerminalFiveLiveSupport
open ECDSAAdd Arithmetic MappedCompressed Challenge OB5
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
attribute [local irreducible] run wires

theorem program_live : wires TerminalInverse23.program ⊆ ((Finset.range 40).erase 38).erase 39 := by
  decide +kernel

def leftIndices : List Nat := [0, 21, 18, 15, 12, 1, 0, 61, 107, 877, 2, 209, 262, 376, 449, 527, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 5, 3, 3, 611, 698, 784, 0, 0]
def rightIndices : List Nat := [2, 2, 13, 14, 15, 16, 17, 1, 1, 0, 7, 8, 9, 10, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 39, 21, 27, 33, 0, 0]

def checkSite (i : Nat) : Bool :=
  if i=38 ∨ i=39 then true else
    let q:=sig 510 (TerminalFiveBridge.perm i)
    WireWitness.atWire (renameProgram (sig 510) Inverse14Width.candidate) q leftIndices[i]! ||
    WireWitness.atWire (renameProgram (sig 506) (W.ReverseCarry.compactReceiverTick base 506)) q rightIndices[i]! ||
    decide (q∈TerminalBorrowB.sites)

theorem sites_checked : (List.range 40).all checkSite=true := by decide +kernel

theorem placed_local : wires (renameProgram (sig 510) TerminalFiveBridge.physical) ⊆
    wires (renameProgram (sig 510) Inverse14Width.candidate) ∪
    wires (renameProgram (sig 506) (W.ReverseCarry.compactReceiverTick base 506)) ∪
    TerminalBorrowB.sites.toFinset := by
  intro q hq
  rw [TerminalFiveBridge.physical,renameProgram_comp,renameProgram_support] at hq
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
  have live:=program_live hi
  have no39 : i≠39 := (Finset.mem_erase.mp live).1
  have next:=(Finset.mem_erase.mp live).2
  have no38 : i≠38 := (Finset.mem_erase.mp next).1
  have small:=Finset.mem_range.mp (Finset.mem_erase.mp next).2
  have table:=List.all_eq_true.mp sites_checked
  have checked:=table i (List.mem_range.mpr small)
  simp only [checkSite,if_neg (not_or.mpr ⟨no38,no39⟩),Bool.or_eq_true,decide_eq_true_eq] at checked
  rcases checked with (h|h)|h
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (WireWitness.atWire_sound _ _ _ h))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (WireWitness.atWire_sound _ _ _ h))
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr h)

end ECDSAAdd.Entrant.TerminalFiveLiveSupport
