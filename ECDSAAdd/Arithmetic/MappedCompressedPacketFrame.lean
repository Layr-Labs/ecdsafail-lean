import ECDSAAdd.Arithmetic.MappedCompressedPacketSupport
import ECDSAAdd.Arithmetic.MappedCompressedCleanTransport

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run

/-- The actual low-width packet implements the original exact field update.
Both clean placement boundaries follow from the encoded frame itself. -/
theorem mappedGroup_encoded_step (divide : Bool) (j : Nat) (hj : j < 170)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (packetLetters j))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (mappedGroup divide j) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (packetLetters j)) (X,Y)).2 out := by
  have reference := baseGroup_encoded_step divide j hj hn hlo ho hp hf origin hg0 hs0 env legal X Y
    (packet_structural_support divide j hj hn hlo) s m input
  have cleanIn := encoded_zero_region base (base 2409) hn hlo origin env X Y s input
  have cleanOut := encoded_zero_region base (base 2409) hn hlo origin env _ _
    (run (baseGroup divide j) m s) reference.2
  have same := mappedGroup_state_eq divide j hj s m cleanIn cleanOut
  change (run (mappedGroup divide j) m s).phase=s.phase ∧ _
  rw [same]
  exact reference

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mappedGroup_encoded_step
