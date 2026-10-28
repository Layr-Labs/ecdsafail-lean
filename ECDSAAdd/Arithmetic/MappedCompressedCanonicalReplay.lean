import ECDSAAdd.Arithmetic.MappedCompressedReplaySpec
import ECDSAAdd.Arithmetic.MappedCompressedCanonicalFrame
import ECDSAAdd.Framework.RunThreeStates
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run mappedReplay converterPairAt directionalPayload
  mixedTranscriptTape mixedTranscriptUnitTrace

/-- The actual middle three blocks of fieldSegment, with both boundary
conversions retained and all history groups encoded at each outer boundary. -/
def canonicalMappedReplay (divide : Bool) : Program :=
  renameProgram allPlaced (converterPair false)++
    (mappedReplay divide++renameProgram allPlaced (converterPair true))

theorem canonicalMappedReplay_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (X Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin X Y s) :
    let out := run (canonicalMappedReplay divide) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)).2 out := by
  let P : State → State → Prop := fun initial out =>
    EncodedCanonicalFrame origin X Y initial → out.phase=initial.phase ∧
      EncodedCanonicalFrame origin
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)).1
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)).2 out
  have all := run_three_states
    (renameProgram allPlaced (converterPair false)) (mappedReplay divide)
    (renameProgram allPlaced (converterPair true)) P
    (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      rw [converterPair_placement] at h1 h3
      have first := encoded_center_pair hn origin hw hu hr hy X Y initial m1 hin
      rw [h1] at first
      have middle := mappedReplay_spec divide hn hlo ho hp hf origin hg0 hs0 env legal X Y s1 m2 first.2
      rw [h2] at middle
      change s3.phase=initial.phase ∧ _
      generalize hQ : directionalPayload (!divide)
        (mixedTranscriptControls origin (base 2400) (mixedTranscriptTape base)) (X,Y)=Q at middle ⊢
      have last := encoded_canonical_pair hn origin hw hu hr hy Q.1 Q.2 s2 m3 middle.2
      rw [h3] at last
      exact ⟨last.1.trans (middle.1.trans first.1),last.2⟩) s m
  exact all input

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.canonicalMappedReplay_spec
