import ECDSAAdd.Arithmetic.MappedCompressedBaseReplay
import ECDSAAdd.Arithmetic.MappedCompressedPacketFrame
import ECDSAAdd.Framework.PacketSequenceFrame
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run mappedGroup baseGroup
attribute [local irreducible] mappedGroups baseGroups measurementCount packetLetters
  mixedTranscriptTape mixedTranscriptUnitTrace

def groupsPayload (divide : Bool) (origin : BasisState) : Nat → Nat → Fp×Fp → Fp×Fp
  | _,0,Q => Q
  | j,n+1,Q =>
      if divide then groupsPayload divide origin (j+1) n
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) Q)
      else directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j))
        (groupsPayload divide origin (j+1) n Q)

private theorem packet_complete (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters j))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    run (mappedGroup divide j) m s=run (baseGroup divide j) m s ∧
    (run (mappedGroup divide j) m s).phase=s.phase ∧
    EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).2
      (run (mappedGroup divide j) m s) := by
  have ref := baseGroup_encoded_step divide j hj hn hlo ho hp hf origin hg0 hs0 env legal X Y
    (packet_structural_support divide j hj hn hlo) s m input
  have cleanIn := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  have cleanOut := encoded_zero_region base (base 2409) hn hlo origin env _ _
    (run (baseGroup divide j) m s) ref.2
  exact ⟨mappedGroup_state_eq divide j hj s m cleanIn cleanOut,
    mappedGroup_encoded_step divide j hj hn hlo ho hp hf origin hg0 hs0 env legal X Y s m input⟩

private theorem mapped_sequence_eq (divide : Bool) (j n : Nat) :
    PacketSequence.program divide (mappedGroup divide) j n=mappedGroups divide j n := by
  induction n generalizing j with
  | zero => simp only [PacketSequence.program,mappedGroups]
  | succ n ih => cases divide <;> simp only [PacketSequence.program,mappedGroups,
      Bool.false_eq_true,if_false,if_true,ih]

private theorem base_sequence_eq (divide : Bool) (j n : Nat) :
    PacketSequence.program divide (baseGroup divide) j n=baseGroups divide j n := by
  induction n generalizing j with
  | zero => simp only [PacketSequence.program,baseGroups]
  | succ n ih => cases divide <;> simp only [PacketSequence.program,baseGroups,
      Bool.false_eq_true,if_false,if_true,ih]

private theorem groups_payload_eq (divide : Bool) (origin : BasisState) (j n : Nat) (Q : Fp×Fp) :
    PacketSequence.payload divide
      (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters k)) V)
      j n Q=groupsPayload divide origin j n Q := by
  induction n generalizing j Q with
  | zero => rfl
  | succ n ih => cases divide <;> simp only [PacketSequence.payload,groupsPayload,
      Bool.false_eq_true,if_false,if_true,ih]

/-- Actual mapped packet contracts instantiate the generic sequence proof.
The complete State and phase agree with the emitted reference replay. -/
theorem mappedGroups_frame (divide : Bool) (j n : Nat) (bound : j+n ≤ 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : ∀k,k < 170 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters k))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (mappedGroups divide j n) m s
    out=run (baseGroups divide j n) m s ∧ out.phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin (groupsPayload divide origin j n (X,Y)).1
        (groupsPayload divide origin j n (X,Y)).2 out := by
  have countEq (k : Nat) : measurementCount (mappedGroup divide k)=measurementCount (baseGroup divide k) :=
    (mappedGroup_counts divide k).2.trans (baseGroup_counts divide k).2.symm
  have all := PacketSequence.frame divide (mappedGroup divide) (baseGroup divide)
    (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters k)) V)
    (fun V t => EncodedFieldFrame base (base 2409) origin V.1 V.2 t) 170 countEq
    (fun k hk V t records h => packet_complete divide k hk hn hlo ho hp (hf k hk)
      origin hg0 hs0 env legal V.1 V.2 t records h) j n bound (X,Y) s m input
  simpa only [mapped_sequence_eq,base_sequence_eq,groups_payload_eq] using all

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mappedGroups_frame
