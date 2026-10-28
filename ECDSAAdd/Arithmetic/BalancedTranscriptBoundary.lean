import ECDSAAdd.Arithmetic.BalancedTranscriptReplay
import ECDSAAdd.Arithmetic.BalancedFieldConvertProof
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
namespace ECDSAAdd.Arithmetic
open Secp256k1 BalancedField

/-- The two boundary conversions reuse scratch, and each restores it. -/
structure BalancedTranscriptBoundary (L : BalancedCircuit.Layout) where
  target : BalancedConvert.Layout
  source : BalancedConvert.Layout
  targetWord : target.word=L.r
  sourceWord : source.word=L.y
  targetWidths : target.Widths
  sourceWidths : source.Widths
  targetND : target.wires.Nodup
  sourceND : source.wires.Nodup
  pairND : (L.r++L.y).Nodup
  targetWorkAway : ∀q∈BalancedConvert.work target,q∉L.r ∧ q∉L.y
  sourceWorkAway : ∀q∈BalancedConvert.work source,q∉L.r ∧ q∉L.y

def balancedTranscriptCenterPair (D : BalancedTranscriptBoundary L) : Program :=
  BalancedConvert.center D.target++BalancedConvert.center D.source

def balancedTranscriptCanonicalPair (D : BalancedTranscriptBoundary L) : Program :=
  BalancedConvert.canonical D.target++BalancedConvert.canonical D.source

def balancedTranscriptCanonicalReplay (L : BalancedCircuit.Layout)
    (D : BalancedTranscriptBoundary L) (b effS : Wire) (ls : List MixedTranscriptLetter) : Program :=
  balancedTranscriptCenterPair D++balancedTranscriptReplay L b effS ls++
    balancedTranscriptCanonicalPair D

private theorem boundary_left (A : BalancedConvert.Layout) (r y : List Wire)
    (he : A.word=r) (hd : r.Disjoint y) (base : BasisState)
    (ha : ∀q∈BalancedConvert.work A,q∉r ∧ q∉y)
    (hc : ∀q∈BalancedConvert.work A,base q=false)
    (I O Y : Nat) (p : Program)
    (correct : ∀s m,regValue A.word s.basis=I →
      (∀q∈BalancedConvert.work A,s.basis q=false) →
      (run p m s).phase=s.phase ∧ regValue A.word (run p m s).basis=O ∧
      (∀q∈BalancedConvert.work A,(run p m s).basis q=false) ∧
      (∀q,q∉A.word → (run p m s).basis q=s.basis q)) :
    Triple (PairFrame r y base I Y) p (PairFrame r y base O Y) := by
  intro s m h
  have clean : ∀q∈BalancedConvert.work A,s.basis q=false := by
    intro q hq
    exact (h.2.2 q (ha q hq).1 (ha q hq).2).trans (hc q hq)
  have v := correct s m (by simpa only [he] using h.1) clean
  exact ⟨v.1,PairFrame.update_temp r y base s.basis (run p m s).basis I Y O hd h
    (by simpa only [he] using v.2.2.2) (by simpa only [he] using v.2.1)⟩

private theorem boundary_right (A : BalancedConvert.Layout) (r y : List Wire)
    (he : A.word=y) (hd : r.Disjoint y) (base : BasisState)
    (ha : ∀q∈BalancedConvert.work A,q∉r ∧ q∉y)
    (hc : ∀q∈BalancedConvert.work A,base q=false)
    (I O X : Nat) (p : Program)
    (correct : ∀s m,regValue A.word s.basis=I →
      (∀q∈BalancedConvert.work A,s.basis q=false) →
      (run p m s).phase=s.phase ∧ regValue A.word (run p m s).basis=O ∧
      (∀q∈BalancedConvert.work A,(run p m s).basis q=false) ∧
      (∀q,q∉A.word → (run p m s).basis q=s.basis q)) :
    Triple (PairFrame r y base X I) p (PairFrame r y base X O) := by
  intro s m h
  have clean : ∀q∈BalancedConvert.work A,s.basis q=false := by
    intro q hq
    exact (h.2.2 q (ha q hq).1 (ha q hq).2).trans (hc q hq)
  have v := correct s m (by simpa only [he] using h.2.1) clean
  exact ⟨v.1,PairFrame.update_dst r y base s.basis (run p m s).basis X I O hd h
    (by simpa only [he] using v.2.2.2) (by simpa only [he] using v.2.1)⟩

theorem balancedTranscriptCenterPair_frame (L : BalancedCircuit.Layout)
    (D : BalancedTranscriptBoundary L) (base : BasisState)
    (ht : ∀q∈BalancedConvert.work D.target,base q=false)
    (hs : ∀q∈BalancedConvert.work D.source,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base X.val Y.val) (balancedTranscriptCenterPair D)
      (PairFrame L.r L.y base (centerWord X) (centerWord Y)) := by
  have dis := (List.nodup_append'.mp D.pairND).2.2
  have t := boundary_left D.target L.r L.y D.targetWord dis base D.targetWorkAway ht
    X.val (centerWord X) Y.val (BalancedConvert.center D.target)
    (BalancedConvert.center_correct D.target D.targetWidths D.targetND X)
  have s := boundary_right D.source L.r L.y D.sourceWord dis base D.sourceWorkAway hs
    Y.val (centerWord Y) (centerWord X) (BalancedConvert.center D.source)
    (BalancedConvert.center_correct D.source D.sourceWidths D.sourceND Y)
  exact t.seq s

theorem balancedTranscriptCanonicalPair_frame (L : BalancedCircuit.Layout)
    (D : BalancedTranscriptBoundary L) (base : BasisState)
    (ht : ∀q∈BalancedConvert.work D.target,base q=false)
    (hs : ∀q∈BalancedConvert.work D.source,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base (centerWord X) (centerWord Y))
      (balancedTranscriptCanonicalPair D) (PairFrame L.r L.y base X.val Y.val) := by
  have dis := (List.nodup_append'.mp D.pairND).2.2
  have t := boundary_left D.target L.r L.y D.targetWord dis base D.targetWorkAway ht
    (centerWord X) X.val (centerWord Y) (BalancedConvert.canonical D.target)
    (BalancedConvert.canonical_correct D.target D.targetWidths D.targetND X)
  have s := boundary_right D.source L.r L.y D.sourceWord dis base D.sourceWorkAway hs
    (centerWord Y) Y.val X.val (BalancedConvert.canonical D.source)
    (BalancedConvert.canonical_correct D.source D.sourceWidths D.sourceND Y)
  exact t.seq s

/-- Canonical words are converted only once on entry and once on exit. -/
theorem balancedTranscriptCanonicalReplay_frame (L : BalancedCircuit.Layout)
    (D : BalancedTranscriptBoundary L) (b effS : Wire) (ls : List MixedTranscriptLetter)
    (hl : BalancedTranscriptReplayLayout L b effS ls) (base : BasisState)
    (hg0 : base L.sign=false) (hs0 : base effS=false)
    (hc : ∀q∈BalancedCircuit.work L,base q=false)
    (ht : ∀q∈BalancedConvert.work D.target,base q=false)
    (hs : ∀q∈BalancedConvert.work D.source,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base X.val Y.val)
      (balancedTranscriptCanonicalReplay L D b effS ls)
      (PairFrame L.r L.y base
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).1.val
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).2.val) := by
  let Q := skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)
  have t := balancedTranscriptCenterPair_frame L D base ht hs X Y
  have r := balancedTranscriptReplay_frame L b effS ls hl base hg0 hs0 hc X Y
  have c := balancedTranscriptCanonicalPair_frame L D base ht hs Q.1 Q.2
  exact (t.seq r).seq c

theorem balancedTranscriptCanonicalReplay_counts (L : BalancedCircuit.Layout)
    (D : BalancedTranscriptBoundary L) (b effS : Wire) (ls : List MixedTranscriptLetter)
    (hl : BalancedTranscriptReplayLayout L b effS ls) :
    toffoliCount (balancedTranscriptCanonicalReplay L D b effS ls)=ls.length*1535+3060 ∧
    measurementCount (balancedTranscriptCanonicalReplay L D b effS ls)=ls.length*1279+3060 := by
  have t := BalancedConvert.counts D.target D.targetWidths
  have s := BalancedConvert.counts D.source D.sourceWidths
  have r := balancedTranscriptReplay_counts L b effS ls hl
  simp only [balancedTranscriptCanonicalReplay,balancedTranscriptCenterPair,
    balancedTranscriptCanonicalPair,toffoliCount_append,measurementCount_append,
    t.1,t.2.1,t.2.2.1,t.2.2.2,s.1,s.2.1,s.2.2.1,s.2.2.2,r.1,r.2]
  omega
end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.balancedTranscriptCanonicalReplay_frame
#print axioms ECDSAAdd.Arithmetic.balancedTranscriptCanonicalReplay_counts
