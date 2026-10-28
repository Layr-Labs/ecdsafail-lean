import ECDSAAdd.Arithmetic.TerminalMappedReplayTrimProof

namespace ECDSAAdd.Arithmetic.EntryInversePayload
open Secp256k1 MappedCompressed CompressedFieldSupport
attribute [local irreducible] groupsPayload indexedLetters trimLetters packetLetters
  mixedTranscriptTape mixedTranscriptUnitTrace

private theorem inverse_append (a b : List (Bool×Bool)) (Q : Fp×Fp) :
    skywalkPayloadReplayInverse (a++b) Q=
      skywalkPayloadReplayInverse a (skywalkPayloadReplayInverse b Q) := by
  induction a with
  | nil => rfl
  | cons l ls ih => simp only [List.cons_append,skywalkPayloadReplayInverse,ih]

private theorem packet_indexed (j : Nat) : packetLetters j=indexedLetters (3*j) 3 := by
  simp [packetLetters,indexedLetters,tapeLetter,List.range_succ]

/-- Packet payload recursion is exactly the original ordered field tape. -/
theorem inverse_groups_payload (j n : Nat) (origin : BasisState) (Q : Fp×Fp) :
    groupsPayload false origin j n Q=
      skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400)
        (indexedLetters (3*j) (3*n))) Q := by
  induction n generalizing j Q with
  | zero => simp only [groupsPayload,indexedLetters,Nat.mul_zero,List.range_zero,List.map_nil,
      mixedTranscriptControls,skywalkPayloadReplayInverse]
  | succ n ih =>
    have len : 3*(n+1)=3+3*n := by omega
    have start : 3*(j+1)=3*j+3 := by omega
    rw [len,indexedLetters_append]
    simp only [groupsPayload,Bool.false_eq_true,if_false,Bool.not_false,directionalPayload,if_true,
      mixedTranscriptControls,List.map_append,inverse_append,ih,start,←packet_indexed]

/-- All170 packets followed by the retained raw510 inverse cell give the
accepted terminal-trim multiplication result, with no new input premise. -/
theorem inverse_boundary (origin : BasisState) (x : Nat) (Y : Fp)
    (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int))) :
    groupsPayload false origin 0 170
      (skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) [tapeLetter 510]) (Y,Y))=
      (2*(if origin (base 2400) then Y*(x:Fp) else Y),0) := by
  have split := indexedLetters_append 0 510 1
  have one : indexedLetters 510 1=[tapeLetter 510] := by
    simp only [indexedLetters,List.range_one,List.map_cons,List.map_nil,Nat.add_zero]
  rw [Nat.zero_add,one] at split
  have shape : trimLetters=indexedLetters 0 510++[tapeLetter 510] := by
    simpa only [trimLetters] using split
  rw [inverse_groups_payload]
  have result := trimLetters_product origin x Y hx0 hx trace
  rw [shape] at result
  simp only [mixedTranscriptControls,List.map_append,inverse_append] at result
  exact result

/-- Removing the final inverse half-add is forced by the existing zero
source result. This algebra is valid for every recorded G/S pair. -/
theorem remove_final_double (g sw : Bool) (Q : Fp×Fp) (Z : Fp)
    (old : skywalkPayloadUncell g sw Q=(2*Z,0)) :
    (if sw then (Q.2,Q.1) else Q)=(Z,0) := by
  let V := if sw then (Q.2,Q.1) else Q
  have value : (2*V.1+(if g then -V.2 else V.2),V.2)=(2*Z,0) := old
  have source : V.2=0 := congrArg Prod.snd value
  have target : 2*V.1=2*Z := by
    have t := congrArg Prod.fst value
    simpa only [source,neg_zero,ite_self,add_zero] using t
  have two : (2:Fp)≠0 := by decide
  have same : V.1=Z := mul_left_cancel₀ two target
  exact Prod.ext same source

end ECDSAAdd.Arithmetic.EntryInversePayload
#print axioms ECDSAAdd.Arithmetic.EntryInversePayload.inverse_groups_payload
#print axioms ECDSAAdd.Arithmetic.EntryInversePayload.inverse_boundary
#print axioms ECDSAAdd.Arithmetic.EntryInversePayload.remove_final_double
