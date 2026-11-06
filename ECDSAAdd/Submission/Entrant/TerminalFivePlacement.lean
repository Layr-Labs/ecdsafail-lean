import ECDSAAdd.Submission.Entrant.TerminalFiveShifted
import ECDSAAdd.Submission.Entrant.TerminalFivePermutation

namespace ECDSAAdd.Entrant.TerminalFivePlacement
open ECDSAAdd Arithmetic MappedCompressed Challenge History5 OB5
open Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run wires Rolling1588.reverse Rolling1588.Integer.reverse

def shiftedReceiver : Program := renameProgram (fun q=>sig 510 (sig 506 q))
  (W.ReverseCarry.compactReceiverTick base 506)

def old : Program := Inverse14Width.candidate ++ shiftedReceiver

theorem shifted_placed : renameProgram (sig 510) shiftedReceiver=
    renameProgram (sig 506) (W.ReverseCarry.compactReceiverTick base 506) := by
  rw [shiftedReceiver,renameProgram_comp]
  have same : (sig 510 ∘ fun q=>sig 510 (sig 506 q))=sig 506 := by
    funext q
    exact sig_invol 510 (by omega) (sig 506 q)
  rw [same]

theorem old_placed : renameProgram (sig 510) old=
    renameProgram (sig 510) Inverse14Width.candidate ++
      renameProgram (sig 506) (W.ReverseCarry.compactReceiverTick base 506) := by
  simp only [old,renameProgram,List.map_append]
  exact congrArg (fun tail=>renameProgram (sig 510) Inverse14Width.candidate ++ tail) shifted_placed

theorem unpack506 (isA : Bool) : unpackFirst base isA 506=[] := by
  simp only [unpackFirst,show ¬(506:Nat)=5 from by decide,if_false,Rolling1588.Integer.decodeBefore,
    show History5.packDue 506=false from by decide,Bool.false_eq_true,if_false]

theorem reverse_shape (isA : Bool) :
    InverseFour15.stackReverse15 isA = renameProgram (sig 511) tickR ++
      (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old) ++
        Rolling1588.reverse isA 1 505) := by
  have shape := reverse_snoc isA 1 505
  rw [show (1:Nat)+505=506 by rfl,unpack506,List.nil_append] at shape
  rw [reverse_eq_packets,reverse_eq_packets] at shape
  rw [InverseFour15.stackReverse15,InverseFour15.reverseTail15,shape]
  have ren (P Q : Program) : renameProgram (sig 510) (P++Q)=
      renameProgram (sig 510) P ++ renameProgram (sig 510) Q := by
    simp only [renameProgram,List.map_append]
  simp only [ren,old_placed,InverseFour15.candidate15,List.append_assoc]

end ECDSAAdd.Entrant.TerminalFivePlacement
