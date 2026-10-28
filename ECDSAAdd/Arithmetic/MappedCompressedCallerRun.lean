import ECDSAAdd.Arithmetic.NativeFirstDirectCallerStates
import ECDSAAdd.Arithmetic.MappedCompressedStageSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace ECDSAAdd.Arithmetic.MappedCompressed
open Secp256k1
attribute [local irreducible] run measurementCount literalSkywalkSeed literalSkywalkUnseed
  compressedCompactForward compressedCompactReverse selectedFieldSegment skywalkArithmeticClear

/-- Complete actual mapped kernel semantics on the existing strong caller
domain, with arbitrary incoming phase and every full measurement record. -/
theorem kernel_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : CompressedHistoryAbove base)
    (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false) :
    DirectSkywalkArithmeticStrong divide base (base 2400) x Y s (run (kernel divide) m s) := by
  simpa only [MappedCompressed.kernel,NativeFirstDirect.callerKernel] using
    NativeFirstDirect.kernel_spec divide hn hlo ho hf x Y hx0 hx s m hin hg0 hs0

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.kernel_spec
