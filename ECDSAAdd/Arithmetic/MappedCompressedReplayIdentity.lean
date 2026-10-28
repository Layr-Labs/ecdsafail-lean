import ECDSAAdd.Arithmetic.MappedCompressedBaseReplay
import ECDSAAdd.Arithmetic.MappedCompressedPacketCorrect

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.MappedCompressed
attribute [local irreducible] logicalCell OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode

def tapeLetter (i : Nat) : MixedTranscriptLetter :=
  (mixedTranscriptTape base).getD i ((0,0),(false,false))

def indexedLetters (start n : Nat) : List MixedTranscriptLetter :=
  (List.range n).map (fun k => tapeLetter (start+k))

private theorem enumerate_getD {α : Type} (ls : List α) (fallback : α) :
    (List.range ls.length).map (fun i => ls.getD i fallback)=ls := by
  induction ls with
  | nil => simp
  | cons a ls ih =>
    rw [List.length_cons,List.range_succ_eq_map]
    simpa only [List.map_cons,List.map_map,Function.comp_def,List.getD_cons_zero,
      List.getD_cons_succ] using congrArg (List.cons a) ih

theorem indexedLetters_full : indexedLetters 0 512=mixedTranscriptTape base := by
  have h := enumerate_getD (mixedTranscriptTape base) ((0,0),(false,false))
  simpa only [mixedTranscriptTape_length,indexedLetters,tapeLetter,Nat.zero_add] using h

private theorem indexedLetters_zero (start : Nat) : indexedLetters start 0=[] := rfl

private theorem indexedLetters_step (start n : Nat) :
    indexedLetters start (n+1)=tapeLetter start::indexedLetters (start+1) n := by
  simp only [indexedLetters,List.range_succ_eq_map,List.map_cons,List.map_map,Function.comp_def]
  simp only [Nat.add_zero,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem indexedLetters_three (start n : Nat) :
    indexedLetters start (n+3)=tapeLetter start::tapeLetter (start+1)::tapeLetter (start+2)::
      indexedLetters (start+3) n := by
  rw [show n+3=(n+2)+1 by omega,indexedLetters_step,
    show n+2=(n+1)+1 by omega,indexedLetters_step,indexedLetters_step]

def referenceCell (divide : Bool) (l : MixedTranscriptLetter) : Program :=
  if divide then OffsetBorrowedCanonical.cell base (base 2400) l.1.1 l.1.2
    (base 2409) (base 2410) l.2.1 l.2.2
  else OffsetBorrowedInverseCanonical.cell base (base 2400) l.1.1 l.1.2
    (base 2409) (base 2410) l.2.1 l.2.2

def referenceGroups (divide : Bool) (start : Nat) (ls : List MixedTranscriptLetter) : Program :=
  if divide then codecGroupForward base (referenceCell divide) start ls
  else codecGroupBackward base (referenceCell divide) start ls

theorem referenceCell_letter (divide : Bool) (i : Nat) (hi : i < 512) :
    referenceCell divide (tapeLetter i)=renameProgram base (logicalCell divide i) := by
  rw [tapeLetter,mixedTape_base_getD i hi,base_cell_eq]
  cases divide <;> rfl

private theorem reference_cons3 (divide : Bool) (start : Nat)
    (a c d : MixedTranscriptLetter) (tail : List MixedTranscriptLetter) :
    referenceGroups divide start (a::c::d::tail)=
      if divide then referenceGroups divide start [a,c,d]++referenceGroups divide (start+3) tail
      else referenceGroups divide (start+3) tail++referenceGroups divide start [a,c,d] := by
  cases divide <;> simp only [referenceGroups,Bool.false_eq_true,if_false,if_true,
    codecGroupForward,codecGroupBackward,List.append_nil,List.nil_append,List.append_assoc]

theorem baseGroup_eq_reference (divide : Bool) (j : Nat) (hj : j < 170) :
    baseGroup divide j=referenceGroups divide (3*j) (packetLetters j) := by
  have packet := baseGroup_eq_packet divide j hj
  cases divide <;> simpa only [referenceGroups,referenceCell,Bool.false_eq_true,if_false,if_true] using packet

private theorem reference_packet_append (divide : Bool) (j : Nat) (hj : j < 170)
    (tail : List MixedTranscriptLetter) :
    referenceGroups divide (3*j) (packetLetters j++tail)=
      if divide then baseGroup divide j++referenceGroups divide (3*j+3) tail
      else referenceGroups divide (3*j+3) tail++baseGroup divide j := by
  have h := reference_cons3 divide (3*j) (tapeLetter (3*j))
    (tapeLetter (3*j+1)) (tapeLetter (3*j+2)) tail
  change referenceGroups divide (3*j) (packetLetters j++tail)=
    (if divide then referenceGroups divide (3*j) (packetLetters j)++referenceGroups divide (3*j+3) tail
     else referenceGroups divide (3*j+3) tail++referenceGroups divide (3*j) (packetLetters j)) at h
  rw [←baseGroup_eq_reference divide j hj] at h
  exact h

theorem baseTail_eq_reference (divide : Bool) :
    baseTail divide=referenceGroups divide 510 (indexedLetters 510 2) := by
  have a := referenceCell_letter divide 510 (by omega)
  have b := referenceCell_letter divide 511 (by omega)
  have letters : indexedLetters 510 2=[tapeLetter 510,tapeLetter 511] := by
    rw [show 2=1+1 by rfl,indexedLetters_step,show 1=0+1 by rfl,indexedLetters_step,indexedLetters_zero]
  rw [letters]
  cases divide <;> simp only [baseTail,referenceGroups,Bool.false_eq_true,if_false,if_true,
    codecGroupForward,codecGroupBackward,a,b]

/-- Structural recursion over all170 packets and the two raw terminal letters.
The tape is reconstructed from its actual getD values, with no body oracle. -/
theorem baseGroups_tail_eq_reference (divide : Bool) (j n : Nat) (h : j+n=170) :
    (if divide then baseGroups divide j n++baseTail divide
     else baseTail divide++baseGroups divide j n)=
      referenceGroups divide (3*j) (indexedLetters (3*j) (3*n+2)) := by
  induction n generalizing j with
  | zero =>
    have hj : j=170 := by omega
    subst j
    simpa only [baseGroups,Nat.mul_zero,Nat.zero_add,Nat.reduceMul,
      List.nil_append,List.append_nil,ite_self] using baseTail_eq_reference divide
  | succ n ih =>
    have rest := ih (j+1) (by omega)
    have split : indexedLetters (3*j) (3*(n+1)+2)=
        packetLetters j++indexedLetters (3*(j+1)) (3*n+2) := by
      rw [show 3*(n+1)+2=(3*n+2)+3 by omega,indexedLetters_three]
      simp only [packetLetters,tapeLetter,List.cons_append,List.nil_append]
      rw [show 3*j+3=3*(j+1) by omega]
    rw [split,reference_packet_append divide j (by omega),
      show 3*j+3=3*(j+1) by omega]
    cases divide <;> simp only [baseGroups,Bool.false_eq_true,if_false,if_true] at rest ⊢
    · rw [←rest]
      simp only [List.append_assoc]
    · rw [←rest]
      simp only [List.append_assoc]

theorem base_forward_replay_identity :
    baseGroups true 0 170++baseTail true=
      compressedFieldForwardGroups base (base 2400) (base 2409) (base 2410) := by
  have h := baseGroups_tail_eq_reference true 0 170 (by omega)
  simpa only [if_true,Nat.mul_zero,Nat.zero_add,Nat.reduceMul,Nat.reduceAdd,indexedLetters_full,
    referenceGroups,referenceCell,compressedFieldForwardGroups] using h

theorem base_backward_replay_identity :
    baseTail false++baseGroups false 0 170=
      compressedFieldBackwardGroups base (base 2400) (base 2409) (base 2410) := by
  have h := baseGroups_tail_eq_reference false 0 170 (by omega)
  simpa only [Bool.false_eq_true,if_false,Nat.mul_zero,Nat.zero_add,Nat.reduceMul,Nat.reduceAdd,
    indexedLetters_full,referenceGroups,referenceCell,compressedFieldBackwardGroups] using h

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.indexedLetters_full
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.base_forward_replay_identity
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.base_backward_replay_identity
