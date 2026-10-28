import ECDSAAdd.Arithmetic.MappedCompressedReplayFrame
import ECDSAAdd.Arithmetic.MappedCompressedEncodedFrameLayout
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run mappedReplay compressedFieldForwardGroups compressedFieldBackwardGroups
  mixedTranscriptTape mixedTranscriptUnitTrace directionalPayload

/-- The entire actual512-cell mapped forward or inverse circuit realizes
the original field replay, with exact incoming phase and encoded workspace.
Packet and residual layouts are derived from the original full tape. -/
theorem mappedReplay_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (mappedReplay divide) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)).2 out := by
  have eq := mappedReplay_reference divide hn hlo ho hp
    (packet_layouts _ _ _ hf) (tail_layout _ _ _ hf) origin hg0 hs0 env legal X Y s m input
  have spec := compressedFieldGroups_512_frame base (base 2400) (base 2409) (base 2410)
    hn hlo ho hp hf origin hg0 hs0 env legal X Y s m input
  cases divide
  · rw [eq]
    simpa only [Bool.false_eq_true,if_false,Bool.not_false,directionalPayload,if_true] using spec.2
  · rw [eq]
    simpa only [if_true,Bool.not_true,directionalPayload,Bool.false_eq_true,if_false] using spec.1

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mappedReplay_spec
