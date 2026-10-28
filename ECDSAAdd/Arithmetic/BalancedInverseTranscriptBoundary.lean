import ECDSAAdd.Arithmetic.BalancedInverseTranscriptReplay
import ECDSAAdd.Arithmetic.BalancedTranscriptBoundary
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
namespace ECDSAAdd.Arithmetic
open Secp256k1 BalancedField

def balancedInverseTranscriptCanonicalReplay (L : BalancedCircuit.Layout)
    (D : BalancedTranscriptBoundary L) (b effS : Wire) (ls : List MixedTranscriptLetter) : Program :=
  balancedTranscriptCenterPair D++balancedInverseTranscriptReplay L b effS ls++
    balancedTranscriptCanonicalPair D

/-- Canonical words are converted only once on entry and once on exit. -/
theorem balancedInverseTranscriptCanonicalReplay_frame (L : BalancedCircuit.Layout)
    (D : BalancedTranscriptBoundary L) (b effS : Wire) (ls : List MixedTranscriptLetter)
    (hl : BalancedTranscriptReplayLayout L b effS ls) (base : BasisState)
    (hg0 : base L.sign=false) (hs0 : base effS=false)
    (hc : ∀q∈BalancedCircuit.work L,base q=false)
    (ht : ∀q∈BalancedConvert.work D.target,base q=false)
    (hs : ∀q∈BalancedConvert.work D.source,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base X.val Y.val)
      (balancedInverseTranscriptCanonicalReplay L D b effS ls)
      (PairFrame L.r L.y base
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).1.val
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).2.val) := by
  let Q := skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)
  have t := balancedTranscriptCenterPair_frame L D base ht hs X Y
  have r := balancedInverseTranscriptReplay_frame L b effS ls hl base hg0 hs0 hc X Y
  have c := balancedTranscriptCanonicalPair_frame L D base ht hs Q.1 Q.2
  exact (t.seq r).seq c

theorem balancedInverseTranscriptCanonicalReplay_counts (L : BalancedCircuit.Layout)
    (D : BalancedTranscriptBoundary L) (b effS : Wire) (ls : List MixedTranscriptLetter)
    (hl : BalancedTranscriptReplayLayout L b effS ls) :
    toffoliCount (balancedInverseTranscriptCanonicalReplay L D b effS ls)=ls.length*1535+3060 ∧
    measurementCount (balancedInverseTranscriptCanonicalReplay L D b effS ls)=ls.length*1279+3060 := by
  have t := BalancedConvert.counts D.target D.targetWidths
  have s := BalancedConvert.counts D.source D.sourceWidths
  have r := balancedInverseTranscriptReplay_counts L b effS ls hl
  simp only [balancedInverseTranscriptCanonicalReplay,balancedTranscriptCenterPair,
    balancedTranscriptCanonicalPair,toffoliCount_append,measurementCount_append,
    t.1,t.2.1,t.2.2.1,t.2.2.2,s.1,s.2.1,s.2.2.1,s.2.2.2,r.1,r.2]
  omega
end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.balancedInverseTranscriptCanonicalReplay_frame
#print axioms ECDSAAdd.Arithmetic.balancedInverseTranscriptCanonicalReplay_counts
