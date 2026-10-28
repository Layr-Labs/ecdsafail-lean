import ECDSAAdd.Arithmetic.BalancedSharedLayoutTranscript
import ECDSAAdd.Arithmetic.BalancedTranscriptTape

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- Exact canonical forward replay on the concrete borrowed shared ports. -/
def balancedSharedCanonicalReplay (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter) : Program :=
  balancedTranscriptCanonicalReplay (balancedSharedPorts w effG)
    (balancedSharedBoundary w effG hn) b effS ls

theorem balancedSharedCanonicalReplay_frame (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b effG effS ls)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base effG=false) (hs0 : base effS=false)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (X Y : Fp) :
    Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base X.val Y.val)
      (balancedSharedCanonicalReplay w b effG effS hn ls)
      (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).1.val
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).2.val) := by
  have hc := balancedSharedPorts_clean w effG base hw hu
  have hb := balancedSharedBoundary_clean w effG base hw hu
  have h := balancedTranscriptCanonicalReplay_frame (balancedSharedPorts w effG)
    (balancedSharedBoundary w effG hn) b effS ls
    (balancedSharedTranscriptReplayLayout w b effG effS ls hf ho)
    base hg0 hs0 hc hb.1 hb.2 X Y
  simpa only [balancedSharedPorts_r,balancedSharedPorts_y,balancedSharedCanonicalReplay] using h

theorem balancedSharedCanonicalReplay_counts (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b effG effS ls)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) :
    toffoliCount (balancedSharedCanonicalReplay w b effG effS hn ls)=ls.length*1535+3060 ∧
    measurementCount (balancedSharedCanonicalReplay w b effG effS hn ls)=ls.length*1279+3060 :=
  balancedTranscriptCanonicalReplay_counts (balancedSharedPorts w effG)
    (balancedSharedBoundary w effG hn) b effS ls
    (balancedSharedTranscriptReplayLayout w b effG effS ls hf ho)

/-- The full 512-record forward division, using original physical controls. -/
def balancedSharedCanonicalTapeReplay (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) : Program :=
  balancedSharedCanonicalReplay w b effG effS hn (mixedTranscriptTape w)

theorem balancedSharedCanonicalTapeReplay_quotient (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : ∀r∈skywalkSharedTape w,MixedTranscriptFieldLayout w b r.1 r.2 effG effS)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base effG=false) (hs0 : base effS=false)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base (2*Y).val 0)
      (balancedSharedCanonicalTapeReplay w b effG effS hn)
      (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base
        (if base b then Y/(x : Fp) else Y).val
        (if base b then Y/(x : Fp) else Y).val) := by
  have h := balancedSharedCanonicalReplay_frame w b effG effS hn (mixedTranscriptTape w)
    (mixedTranscriptTape_layout w b effG effS hf) ho base hg0 hs0 hw hu (2*Y) 0
  rw [mixedTranscriptTape_quotient w base b x Y hx0 hx hr] at h
  exact h

theorem balancedSharedCanonicalTapeReplay_counts (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : ∀r∈skywalkSharedTape w,MixedTranscriptFieldLayout w b r.1 r.2 effG effS)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) :
    toffoliCount (balancedSharedCanonicalTapeReplay w b effG effS hn)=788980 ∧
    measurementCount (balancedSharedCanonicalTapeReplay w b effG effS hn)=657908 := by
  have h := balancedSharedCanonicalReplay_counts w b effG effS hn (mixedTranscriptTape w)
    (mixedTranscriptTape_layout w b effG effS hf) ho
  simpa only [mixedTranscriptTape_length,Nat.reduceMul,Nat.reduceAdd] using h

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.balancedSharedCanonicalReplay_frame
#print axioms ECDSAAdd.Arithmetic.balancedSharedCanonicalTapeReplay_quotient
#print axioms ECDSAAdd.Arithmetic.balancedSharedCanonicalTapeReplay_counts
