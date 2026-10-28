import ECDSAAdd.Arithmetic.BalancedTranscriptBoundary
namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- Full 512-record forward field replay, including the inactive unit trace. -/
def balancedTranscriptTapeReplay (w : Nat → Wire) (L : BalancedCircuit.Layout)
    (D : BalancedTranscriptBoundary L) (b effS : Wire) : Program :=
  balancedTranscriptCanonicalReplay L D b effS (mixedTranscriptTape w)

theorem balancedTranscriptTapeReplay_quotient (w : Nat → Wire)
    (L : BalancedCircuit.Layout) (D : BalancedTranscriptBoundary L) (b effS : Wire)
    (hl : BalancedTranscriptReplayLayout L b effS (mixedTranscriptTape w))
    (base : BasisState) (hg0 : base L.sign=false) (hs0 : base effS=false)
    (hc : ∀q∈BalancedCircuit.work L,base q=false)
    (ht : ∀q∈BalancedConvert.work D.target,base q=false)
    (hs : ∀q∈BalancedConvert.work D.source,base q=false)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    Triple (PairFrame L.r L.y base (2*Y).val 0)
      (balancedTranscriptTapeReplay w L D b effS)
      (PairFrame L.r L.y base
        (if base b then Y/(x : Fp) else Y).val
        (if base b then Y/(x : Fp) else Y).val) := by
  have replay := balancedTranscriptCanonicalReplay_frame L D b effS (mixedTranscriptTape w)
    hl base hg0 hs0 hc ht hs (2*Y) 0
  rw [mixedTranscriptTape_quotient w base b x Y hx0 hx hr] at replay
  exact replay

theorem balancedTranscriptTapeReplay_counts (w : Nat → Wire)
    (L : BalancedCircuit.Layout) (D : BalancedTranscriptBoundary L) (b effS : Wire)
    (hl : BalancedTranscriptReplayLayout L b effS (mixedTranscriptTape w)) :
    toffoliCount (balancedTranscriptTapeReplay w L D b effS)=788980 ∧
    measurementCount (balancedTranscriptTapeReplay w L D b effS)=657908 := by
  have h := balancedTranscriptCanonicalReplay_counts L D b effS (mixedTranscriptTape w) hl
  simpa only [mixedTranscriptTape_length,Nat.reduceMul,Nat.reduceAdd] using h
end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.balancedTranscriptTapeReplay_quotient
#print axioms ECDSAAdd.Arithmetic.balancedTranscriptTapeReplay_counts
