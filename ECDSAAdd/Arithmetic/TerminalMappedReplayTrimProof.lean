import ECDSAAdd.Arithmetic.TerminalMappedReplayReference
import ECDSAAdd.Arithmetic.MappedCompressedReplaySpec
import ECDSAAdd.Arithmetic.PairFrameUnique

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run trimReplay baseTrimReplay mappedReplay mixedTranscriptTape
  mixedTranscriptUnitTrace directionalPayload indexedLetters trimLetters

/-- The511 actual field cells retain the full fixed170-group encoding,
including phase and every work/control/source-frame bit. -/
theorem trimReplay_frame (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin) (X Y : Fp)
    (s : State) (m : List Bool) (input : EncodedFieldFrame base (base 2409) origin X Y s) :
    let out := run (trimReplay divide) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) trimLetters) (X,Y)).1
      (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) trimLetters) (X,Y)).2 out := by
  have eq := trimReplay_reference divide hn hlo ho hp hf origin hg0 hs0 env legal X Y s m input
  have len : trimLetters.length=3*170+1 := by
    simp only [trimLetters,indexedLetters,List.length_map,List.length_range]
  have ref := trim_grouped_encoded_replays base (base 2400) (base 2409) (base 2410)
    hn hlo ho hp origin hg0 hs0 env legal 170 0 (by decide) trimLetters len trimLetters_indexed
    (trimLetters_layout hf)
  rw [eq,baseTrimReplay_reference]
  cases divide
  · simpa only [referenceGroups,referenceCell,Bool.false_eq_true,if_false,Bool.not_false,
      directionalPayload,if_true] using ref.2 X Y s m input
  · simpa only [referenceGroups,referenceCell,if_true,Bool.not_true,directionalPayload,
      Bool.false_eq_true,if_false] using ref.1 X Y s m input

private theorem encoded_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (phase : s.phase=t.phase)
    (hs : EncodedFieldFrame base (base 2409) origin X Y s)
    (ht : EncodedFieldFrame base (base 2409) origin X Y t) : s=t := by
  obtain ⟨a,pa,fa,ea⟩ := hs
  obtain ⟨b,pb,fb,eb⟩ := ht
  have raw : a=b := by
    apply State.extensionality
    · exact pa.trans (phase.trans pb.symm)
    · exact PairFrame.unique _ _ origin _ _ a.basis b.basis fa fb
  rw [ea,eb,raw]

def trimInput (divide : Bool) (Y : Fp) : Fp×Fp := if divide then (2*Y,0) else (Y,Y)
def trimOutput (divide : Bool) (origin : BasisState) (x : Nat) (Y : Fp) : Fp×Fp :=
  if divide then
    (if origin (base 2400) then Y/(x : Fp) else Y,
     if origin (base 2400) then Y/(x : Fp) else Y)
  else (2*(if origin (base 2400) then Y*(x : Fp) else Y),0)

/-- The public specialization uses the original canonical nonzero divisor
and actual512 signed-trace premise. No new terminal-state input is required. -/
theorem trimReplay_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)))
    (s : State) (m : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin (trimInput divide Y).1 (trimInput divide Y).2 s) :
    let out := run (trimReplay divide) m s
    out.phase=s.phase ∧ EncodedFieldFrame base (base 2409) origin
      (trimOutput divide origin x Y).1 (trimOutput divide origin x Y).2 out := by
  have frame := trimReplay_frame divide hn hlo ho hp hf origin hg0 hs0 env legal
    (trimInput divide Y).1 (trimInput divide Y).2 s m input
  cases divide
  · simpa only [trimInput,trimOutput,Bool.false_eq_true,if_false,Bool.not_false,
      directionalPayload,if_true,trimLetters_product origin x Y hx0 hx hr] using frame
  · simpa only [trimInput,trimOutput,if_true,Bool.not_true,directionalPayload,
      Bool.false_eq_true,if_false,trimLetters_quotient origin x Y hx0 hx hr] using frame

/-- Independent records for the new511-cell and legacy512-cell programs
produce exactly the same complete State on the actual caller trajectory. -/
theorem trimReplay_old_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)))
    (s : State) (m k : List Bool)
    (input : EncodedFieldFrame base (base 2409) origin (trimInput divide Y).1 (trimInput divide Y).2 s) :
    run (trimReplay divide) m s=run (mappedReplay divide) k s := by
  have a := trimReplay_spec divide hn hlo ho hp hf origin hg0 hs0 env legal x Y hx0 hx hr s m input
  have b := mappedReplay_spec divide hn hlo ho hp hf origin hg0 hs0 env legal
    (trimInput divide Y).1 (trimInput divide Y).2 s k input
  have old : (run (mappedReplay divide) k s).phase=s.phase ∧
      EncodedFieldFrame base (base 2409) origin
        (trimOutput divide origin x Y).1 (trimOutput divide origin x Y).2
        (run (mappedReplay divide) k s) := by
    cases divide
    · simpa only [trimInput,trimOutput,Bool.false_eq_true,if_false,Bool.not_false,
        directionalPayload,if_true,mixedTranscriptTape_product base origin (base 2400) x Y hx0 hx hr] using b
    · simpa only [trimInput,trimOutput,if_true,Bool.not_true,directionalPayload,
        Bool.false_eq_true,if_false,mixedTranscriptTape_quotient base origin (base 2400) x Y hx0 hx hr] using b
  exact encoded_unique origin _ _ _ _ (a.1.trans old.1.symm) a.2 old.2

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.trimReplay_frame
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.trimReplay_spec
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.trimReplay_old_eq
