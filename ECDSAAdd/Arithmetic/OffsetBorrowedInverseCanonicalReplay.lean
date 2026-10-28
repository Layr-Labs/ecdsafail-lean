import ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonicalCell
import ECDSAAdd.Arithmetic.BalancedInverseSharedReplay
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical
open Secp256k1 BalancedField OffsetBorrowedCanonical

private theorem selected_other (base : BasisState) (b source flag q : Wire) (v : Bool)
    (hne : q≠flag) : mixedTranscriptBase base b source flag v q=base q := by
  simp only [mixedTranscriptBase,writeBit,Function.update_of_ne hne]

/-- Both mixed selection windows clean their controls and preserve phase
for the recorded or inactive choice on every measurement record. -/
theorem cell_frame (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign=false) (hs0 : base effS=false)
    (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (cell w b g swap sign effS ig is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadUncell (mixedTranscriptBit base b g ig)
          (mixedTranscriptBit base b swap is) (X,Y)).1)
        (centerWord (skywalkPayloadUncell (mixedTranscriptBit base b g ig)
          (mixedTranscriptBit base b swap is) (X,Y)).2)) := by
  let L := balancedSharedPorts w sign
  let bg := mixedTranscriptBase base b g sign ig
  let bs := mixedTranscriptBase bg b swap effS is
  have sg : [b,g,sign].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hl.controls q
    simp only [balancedSharedPorts,List.count_cons,List.count_nil] at h ⊢
    omega
  have ss : [b,swap,effS].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hl.controls q
    simp only [balancedSharedPorts,List.count_cons,List.count_nil] at h ⊢
    omega
  have d0 := List.nodup_cons.mp hl.controls
  have d1 := List.nodup_cons.mp d0.2
  have d2 := List.nodup_cons.mp d1.2
  have d3 := List.nodup_cons.mp d2.2
  have ne : effS≠sign := Ne.symm (by simpa using d3.1)
  have bn : b≠sign := by
    have h := (List.nodup_cons.mp sg).1
    intro e; exact h (by simp [e])
  have sn : swap≠sign := by
    intro e
    exact d2.1 (by simp [balancedSharedPorts,e])
  have bgS : bg effS=false := (selected_other _ _ _ _ _ _ ne).trans hs0
  have bgB : bg b=base b := selected_other _ _ _ _ _ _ bn
  have bgSwap : bg swap=base swap := selected_other _ _ _ _ _ _ sn
  have bsG : bs sign=mixedTranscriptBit base b g ig := by
    rw [show bs sign=bg sign from selected_other _ _ _ _ _ _ (Ne.symm ne)]
    simp only [bg,mixedTranscriptBase,writeBit,Function.update_self]
  have bsS : bs effS=mixedTranscriptBit base b swap is := by
    simp only [bs,mixedTranscriptBase,writeBit,Function.update_self,mixedTranscriptBit,bgB,bgSwap]
  have ge : Env w bg := env_write w sign ho base _ he
  have se : Env w bs := env_write w effS hoS bg _ ge
  have bd := body_frame w sign effS hn ho hl.swapND bs se X Y
  rw [bsG,bsS] at bd
  have inner := transcriptSelectWindow_pairFrame b swap effS is L.r L.y ss
    (hl.outside b (by simp)) (hl.outside swap (by simp))
    (hl.outside effS (by simp)) bg bgS (centerWord X) (centerWord Y) _ _ _ bd
  exact transcriptSelectWindow_pairFrame b g sign ig L.r L.y sg
    (hl.outside b (by simp)) (hl.outside g (by simp)) (hl.outside sign (by simp [balancedSharedPorts]))
    base hg0 _ _ _ _ _ inner

/-- Arithmetic inverse cells run in reverse transcript order. No MX is reversed. -/
def replay (w : Nat → Wire) (b sign effS : Wire) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => replay w b sign effS ls++cell w b l.1.1 l.1.2 sign effS l.2.1 l.2.2

def canonicalReplay (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter) : Program :=
  balancedTranscriptCenterPair (balancedSharedBoundary w sign hn)++replay w b sign effS ls++
    balancedTranscriptCanonicalPair (balancedSharedBoundary w sign hn)

theorem replay_frame (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base sign=false) (hs0 : base effS=false) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (replay w b sign effS ls)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).1)
        (centerWord (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).2)) := by
  induction ls generalizing X Y with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons l ls ih =>
    let Q := skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)
    have r := ih (fun q hq => hf q (by simp [hq])) X Y
    have c := cell_frame w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hn
      (balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 sign effS (hf l (by simp)) ho)
      (ho sign (by simp)) (ho effS (by simp)) base hg0 hs0 he Q.1 Q.2
    simpa only [replay,mixedTranscriptControls,List.map_cons,skywalkPayloadReplayInverse,Q] using r.seq c

/-- Public canonical inverse frame with caller-derived high-zero. The
original full257 canonical source supplies Env at every framed boundary. -/
theorem canonicalReplay_frame (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base sign=false) (hs0 : base effS=false)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (original : Fp)
    (hOriginal : regValue (skywalkSharedField w).a base=original.val) (X Y : Fp) :
    Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base X.val Y.val)
      (canonicalReplay w b sign effS hn ls)
      (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).1.val
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).2.val) := by
  let L := balancedSharedPorts w sign
  let D := balancedSharedBoundary w sign hn
  let Q := skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)
  have clean := balancedSharedBoundary_clean w sign base hw hu
  have a := balancedTranscriptCenterPair_frame L D base clean.1 clean.2 X Y
  have r := replay_frame w b sign effS hn ls hf ho base hg0 hs0
    (env_of_canonical_source w hn base original hOriginal hw hu) X Y
  have c := balancedTranscriptCanonicalPair_frame L D base clean.1 clean.2 Q.1 Q.2
  simpa only [canonicalReplay,L,D,Q,balancedSharedPorts_r,balancedSharedPorts_y] using (a.seq r).seq c

theorem replay_counts (w : Nat → Wire) (b sign effS : Wire)
    (_hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) :
    toffoliCount (replay w b sign effS ls)=ls.length*1281 ∧
    measurementCount (replay w b sign effS ls)=ls.length*1025 := by
  induction ls with
  | nil => simp [replay,toffoliCount,measurementCount]
  | cons l ls ih =>
    have hl := balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 sign effS (hf l (by simp)) ho
    have c := cell_counts w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hl.swapND
    have r := ih (fun q hq => hf q (by simp [hq]))
    change toffoliCount (replay w b sign effS ls++
        cell w b l.1.1 l.1.2 sign effS l.2.1 l.2.2)=(ls.length+1)*1281 ∧
      measurementCount (replay w b sign effS ls++
        cell w b l.1.1 l.1.2 sign effS l.2.1 l.2.2)=(ls.length+1)*1025
    rw [toffoliCount_append,measurementCount_append,r.1,r.2,c.1,c.2]
    constructor <;> simp only [Nat.add_mul,Nat.one_mul]

theorem canonicalReplay_counts (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) :
    toffoliCount (canonicalReplay w b sign effS hn ls)=ls.length*1281+3060 ∧
    measurementCount (canonicalReplay w b sign effS hn ls)=ls.length*1025+3060 := by
  let D := balancedSharedBoundary w sign hn
  have t := BalancedConvert.counts D.target D.targetWidths
  have s := BalancedConvert.counts D.source D.sourceWidths
  have r := replay_counts w b sign effS hn ls hf ho
  simp only [canonicalReplay,balancedTranscriptCenterPair,balancedTranscriptCanonicalPair,
    toffoliCount_append,measurementCount_append]
  change (toffoliCount (BalancedConvert.center D.target)+toffoliCount (BalancedConvert.center D.source)+
      toffoliCount (replay w b sign effS ls)+
      (toffoliCount (BalancedConvert.canonical D.target)+toffoliCount (BalancedConvert.canonical D.source)))
      =ls.length*1281+3060 ∧ _
  rw [t.1,t.2.1,t.2.2.1,t.2.2.2,s.1,s.2.1,s.2.2.1,s.2.2.2,r.1,r.2]
  constructor <;> omega

def canonicalTapeReplay (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) : Program :=
  canonicalReplay w b sign effS hn (mixedTranscriptTape w)

theorem canonicalTapeReplay_product (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : MixedTranscriptReplayLayout w b sign effS (mixedTranscriptTape w))
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base sign=false) (hs0 : base effS=false)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (original : Fp)
    (hOriginal : regValue (skywalkSharedField w).a base=original.val)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base Y.val Y.val)
      (canonicalTapeReplay w b sign effS hn)
      (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base
        (2*(if base b then Y*(x : Fp) else Y)).val 0) := by
  have r := canonicalReplay_frame w b sign effS hn (mixedTranscriptTape w) hf ho base
    hg0 hs0 hw hu original hOriginal Y Y
  rw [mixedTranscriptTape_product w base b x Y hx0 hx hr] at r
  exact r

theorem canonicalTapeReplay_counts (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : MixedTranscriptReplayLayout w b sign effS (mixedTranscriptTape w))
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) :
    toffoliCount (canonicalTapeReplay w b sign effS hn)=658932 ∧
    measurementCount (canonicalTapeReplay w b sign effS hn)=527860 := by
  have h := canonicalReplay_counts w b sign effS hn (mixedTranscriptTape w) hf ho
  simpa only [canonicalTapeReplay,mixedTranscriptTape_length,Nat.reduceMul,Nat.reduceAdd] using h

end ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical.cell_frame
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical.canonicalReplay_frame
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical.canonicalTapeReplay_product
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical.canonicalTapeReplay_counts
