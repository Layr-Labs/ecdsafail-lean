import ECDSAAdd.Arithmetic.TerminalMappedReplayTrimProof
import ECDSAAdd.Arithmetic.MappedCompressedFieldSegmentSpec
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run trimReplay converterPairAt directionalPayload
  mixedTranscriptTape mixedTranscriptUnitTrace
/-- The actual middle three blocks of fieldSegment, with both boundary
conversions retained and all history groups encoded at each outer boundary. -/
def canonicalTrimReplay (divide : Bool) : Program :=
  renameProgram allPlaced (converterPair false)++
    (trimReplay divide++renameProgram allPlaced (converterPair true))

theorem canonicalTrimReplay_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int))) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin (trimInput divide Y).1 (trimInput divide Y).2 s) :
    let out := run (canonicalTrimReplay divide) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin
      (trimOutput divide origin x Y).1
      (trimOutput divide origin x Y).2 out := by
  let P : State → State → Prop := fun initial out =>
    EncodedCanonicalFrame origin (trimInput divide Y).1 (trimInput divide Y).2 initial → out.phase=initial.phase ∧
      EncodedCanonicalFrame origin
        (trimOutput divide origin x Y).1
        (trimOutput divide origin x Y).2 out
  have all := run_three_states
    (renameProgram allPlaced (converterPair false)) (trimReplay divide)
    (renameProgram allPlaced (converterPair true)) P
    (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      rw [converterPair_placement] at h1 h3
      have first := encoded_center_pair hn origin hw hu hr hy (trimInput divide Y).1 (trimInput divide Y).2 initial m1 hin
      rw [h1] at first
      have middle := trimReplay_spec divide hn hlo ho hp hf origin hg0 hs0 env legal x Y hx0 hx trace s1 m2 first.2
      rw [h2] at middle
      change s3.phase=initial.phase ∧ _
      generalize hQ : trimOutput divide origin x Y=Q at middle ⊢
      have last := encoded_canonical_pair hn origin hw hu hr hy Q.1 Q.2 s2 m3 middle.2
      rw [h3] at last
      exact ⟨last.1.trans (middle.1.trans first.1),last.2⟩) s m
  exact all input


/-- Actual retained outer endpoints and conversions, with only the proven
terminal field cell omitted. Native integer recording still has512 rounds. -/
def fieldTrimSegment (divide : Bool) : Program :=
  fieldPrefix divide++(canonicalTrimReplay divide++fieldSuffix divide)

/-- Complete actual mapped field segment: both retained endpoints and both
conversions surround the511 field replay; native recording stays512. All records preserve phase,
the encoded transcript, and the clean original source port. -/
theorem fieldTrimSegment_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    let out := run (fieldTrimSegment divide) m s
    out.phase=s.phase ∧ EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out := by
  let P : State → State → Prop := fun initial out => EncodedCanonicalFrame origin Y 0 initial →
    out.phase=initial.phase ∧ EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out
  have all := run_three_states (fieldPrefix divide) (canonicalTrimReplay divide) (fieldSuffix divide) P
    (by
      intro initial s1 s2 s3 m1 m2 m3 h1 h2 h3 hin
      cases divide
      · simp only [fieldPrefix,fieldSuffix,Bool.false_eq_true,if_false] at h1 h3
        have first := mapped_copy_fill hn origin Y initial m1 hin
        rw [h1] at first
        have middle := canonicalTrimReplay_spec false hn hlo ho hp hf origin hg0 hs0 env legal
          hw hu hr hy x Y hx0 hx trace s1 m2 first.2
        rw [h2] at middle
        simp only [trimOutput,Bool.false_eq_true,if_false] at middle
        let Z := if origin (base 2400) then Y*(x:Fp) else Y
        have last := mapped_unary_step false hn hlo origin hw hu (2*Z) 0 s2 m3 middle.2
        simp only [Bool.false_eq_true,if_false] at last
        rw [h3] at last
        have two : (2:Fp)≠0 := by decide
        have halve : (2*Z)/2=Z := by rw [mul_comm 2 Z,mul_div_cancel_right₀ Z two]
        rw [halve] at last
        exact ⟨last.1.trans (middle.1.trans first.1),by simpa only [fieldResult,Bool.false_eq_true,if_false,Z] using last.2⟩
      · simp only [fieldPrefix,fieldSuffix,if_true] at h1 h3
        have first := mapped_unary_step true hn hlo origin hw hu Y 0 initial m1 hin
        simp only [if_true] at first
        rw [h1] at first
        have middle := canonicalTrimReplay_spec true hn hlo ho hp hf origin hg0 hs0 env legal
          hw hu hr hy x Y hx0 hx trace s1 m2 first.2
        rw [h2] at middle
        simp only [trimOutput,if_true] at middle
        let Z := if origin (base 2400) then Y/(x:Fp) else Y
        have last := mapped_copy_clear hn origin Z s2 m3 middle.2
        rw [h3] at last
        exact ⟨last.1.trans (middle.1.trans first.1),by simpa only [fieldResult,if_true,Z] using last.2⟩) s m
  exact all input

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.canonicalTrimReplay_spec
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.fieldTrimSegment_spec
