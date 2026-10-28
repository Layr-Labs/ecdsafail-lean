import ECDSAAdd.Arithmetic.MappedCompressedFieldPoolRestore
import ECDSAAdd.Arithmetic.EntryForwardSelectedFieldSegment
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1 DirectSkywalk OffsetBorrowedCanonical CompressedFieldSupport
attribute [local irreducible] run selectedFieldSegment skywalkArithmeticClear
  compressedCompactForward compressedCompactReverse
theorem selectedFieldSegment_pool_frame (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : EncodedCanonicalFrame origin Y 0 s) :
    (run (selectedFieldSegment divide) m s).phase=s.phase ∧
      ∀q∈skywalkPoolWires base,(run (selectedFieldSegment divide) m s).basis q=s.basis q := by
  have result := selectedFieldSegment_spec divide hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy x hx0 hx trace Y s m input
  have before := encodedCanonical_pool_basis hn hlo origin ha Y s input
  have after := encodedCanonical_pool_basis hn hlo origin ha _ (run (selectedFieldSegment divide) m s) result.2
  exact ⟨result.1,fun q hq => (after q hq).trans (before q hq).symm⟩

theorem selectedFieldSegment_reverse_pool (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : RawGroupLegal base 170 origin)
    (hw : regValue (skywalkSharedField base).work origin=0)
    (hu : regValue (skywalkSharedUnused base) origin=0)
    (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (initial : State) (mForward mFirst mField mLast mReverse : List Bool)
    (hin : SkywalkIntegerStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 0 initial.basis)
    (input : EncodedCanonicalFrame origin Y 0
      (run (skywalkArithmeticClear base) mFirst (run (compressedCompactForward base 0 512) mForward initial))) :
    let recorded := run (compressedCompactForward base 0 512) mForward initial
    let prepared := run (skywalkArithmeticClear base) mFirst recorded
    let field := run (selectedFieldSegment divide) mField prepared
    let restored := run (skywalkArithmeticClear base) mLast field
    (run (compressedCompactReverse base 0 512) mReverse restored).phase=initial.phase ∧
      (∀q∈skywalkPoolWires base,(run (compressedCompactReverse base 0 512) mReverse restored).basis q=initial.basis q) ∧
      (∀q,q∉skywalkPoolWires base →
        (run (compressedCompactReverse base 0 512) mReverse restored).basis q=restored.basis q) := by
  let recorded := run (compressedCompactForward base 0 512) mForward initial
  let prepared := run (skywalkArithmeticClear base) mFirst recorded
  let field := run (selectedFieldSegment divide) mField prepared
  let restored := run (skywalkArithmeticClear base) mLast field
  have keeps := selectedFieldSegment_pool_frame divide hn hlo ho hp hf origin hg0 hs0 env legal
    hw hu hr hy ha x hx0 hx trace Y prepared mField input
  have recovered := clear_after_pool_update hn recorded field mFirst mLast keeps.1 keeps.2
  exact compressedCompactReverse_restore_after_outside base (skywalkShared_integer_nodup base hn)
    hlo x p (by norm_num [p]) hx0 (by norm_num [p]) (by norm_num [p]) hx
    (arith_coprime x hx0 hx) initial restored mForward mReverse hin recovered.1 recovered.2

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.selectedFieldSegment_pool_frame
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.selectedFieldSegment_reverse_pool
