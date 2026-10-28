import ECDSAAdd.Arithmetic.MappedCompressedPacketTransport
import ECDSAAdd.Arithmetic.CompressedFieldGroupedReplay
import ECDSAAdd.Arithmetic.FieldRenameCells
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run

private theorem zip_range_getD (w : Nat → Wire) (n start i : Nat) (hi : i < n)
    (cs : List (Bool×Bool)) (hc : cs.length=n) (fallback : MixedTranscriptLetter) :
    (((List.range n).map (fun k => (w (start+k),w (1028+start+k)))).zip cs).getD i fallback =
      ((w (start+i),w (1028+start+i)),cs.getD i (false,false)) := by
  induction n generalizing start i cs with
  | zero => omega
  | succ n ih =>
    cases cs with
    | nil => simp at hc
    | cons c cs =>
      have len : cs.length=n := by simpa using hc
      rw [List.range_succ_eq_map,List.map_cons,List.zip_cons_cons]
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.getD_cons_succ]
        simpa only [List.map_map,Function.comp_def,Nat.succ_eq_add_one,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (start+1) i (by omega) cs len

/-- Both coordinates and inactive unit-trace bits are those of the actual
original512 mixed tape, including every valid last packet index. -/
theorem mixedTape_base_getD (i : Nat) (hi : i < 512) :
    (mixedTranscriptTape base).getD i ((0,0),(false,false)) =
      ((base i,base (1028+i)),mixedTranscriptUnitTrace.getD i (false,false)) := by
  simpa only [mixedTranscriptTape,skywalkSharedTape,Nat.zero_add] using
    zip_range_getD base 512 0 i hi mixedTranscriptUnitTrace mixedTranscriptUnitTrace_length ((0,0),(false,false))

def packetLetters (j : Nat) : List MixedTranscriptLetter :=
  [(mixedTranscriptTape base).getD (3*j) ((0,0),(false,false)),
   (mixedTranscriptTape base).getD (3*j+1) ((0,0),(false,false)),
   (mixedTranscriptTape base).getD (3*j+2) ((0,0),(false,false))]

/-- Exact emitted instructions, including every measurement correction:
the base relabeling is a natural relabeling of this finite field cell. -/
theorem base_cell_eq (divide : Bool) (i : Nat) :
    renameProgram base (logicalCell divide i) =
      (if divide then OffsetBorrowedCanonical.cell base (base 2400) (base i) (base (1028+i))
          (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD i (false,false)).1
          (mixedTranscriptUnitTrace.getD i (false,false)).2
       else OffsetBorrowedInverseCanonical.cell base (base 2400) (base i) (base (1028+i))
          (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD i (false,false)).1
          (mixedTranscriptUnitTrace.getD i (false,false)).2) := by
  exact FieldRename.logical_cell_natural base divide i

/-- This is the actual base packet used by mappedGroup, not a postulated
body oracle. The raw control letters and unit constants match the mixed tape. -/
theorem baseGroup_eq_packet (divide : Bool) (j : Nat) (hj : j < 170) :
    baseGroup divide j =
      (if divide then codecGroupForward base (fun l : MixedTranscriptLetter =>
          OffsetBorrowedCanonical.cell base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) l.2.1 l.2.2)
          (3*j) (packetLetters j)
       else codecGroupBackward base (fun l : MixedTranscriptLetter =>
          OffsetBorrowedInverseCanonical.cell base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) l.2.1 l.2.2)
          (3*j) (packetLetters j)) := by
  have a := mixedTape_base_getD (3*j) (by omega)
  have c := mixedTape_base_getD (3*j+1) (by omega)
  have d := mixedTape_base_getD (3*j+2) (by omega)
  cases divide <;> simp only [baseGroup,packetLetters,a,c,d,codecGroupForward,codecGroupBackward,
    base_cell_eq,Bool.false_eq_true,if_false,if_true,List.append_nil,List.nil_append,List.append_assoc]

/-- Complete semantic bridge for the actual baseGroup, over the fixed170
encoding. The only body premise is actual static support, which follows from
its current-index cell support; no circuit-correctness assumption is added. -/
theorem baseGroup_encoded_step (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters j))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (support : wires (if divide then rawForwardPacket base (base 2400) (base 2409) (base 2410)
        ((packetLetters j).getD 0 ((0,0),(false,false))) ((packetLetters j).getD 1 ((0,0),(false,false)))
        ((packetLetters j).getD 2 ((0,0),(false,false)))
      else rawBackwardPacket base (base 2400) (base 2409) (base 2410)
        ((packetLetters j).getD 0 ((0,0),(false,false))) ((packetLetters j).getD 1 ((0,0),(false,false)))
        ((packetLetters j).getD 2 ((0,0),(false,false)))) ⊆
      groupReadSites base (base 2400) (base 2409) (base 2410) (3*j))
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (baseGroup divide j) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).2 out := by
  let a := (mixedTranscriptTape base).getD (3*j) ((0,0),(false,false))
  let c := (mixedTranscriptTape base).getD (3*j+1) ((0,0),(false,false))
  let d := (mixedTranscriptTape base).getD (3*j+2) ((0,0),(false,false))
  cases divide
  · have step := encoded_backward_packet_step base (base 2400) (base 2409) (base 2410) hn hlo j hj a c d
      hf ho hp origin hg0 hs0 env legal X Y (by simpa [packetLetters] using support) s m input
    rw [baseGroup_eq_packet false j hj]
    simpa only [packetLetters,directionalPayload,Bool.not_false,if_true,a,c,d] using step
  · have step := encoded_forward_packet_step base (base 2400) (base 2409) (base 2410) hn hlo j hj a c d
      hf ho hp origin hg0 hs0 env legal X Y (by simpa [packetLetters] using support) s m input
    rw [baseGroup_eq_packet true j hj]
    simpa only [packetLetters,directionalPayload,Bool.not_true,Bool.false_eq_true,if_false,a,c,d] using step

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mixedTape_base_getD
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.base_cell_eq
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.baseGroup_eq_packet
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.baseGroup_encoded_step
