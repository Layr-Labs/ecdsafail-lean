import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalCell
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedCanonical
open Secp256k1 BalancedField

theorem cell_frame (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base sign=false) (hs0 : base effS=false)
    (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (cell w b g swap sign effS ig is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadCell (mixedTranscriptBit base b g ig)
          (mixedTranscriptBit base b swap is) (X,Y)).1)
        (centerWord (skywalkPayloadCell (mixedTranscriptBit base b g ig)
          (mixedTranscriptBit base b swap is) (X,Y)).2)) := by
  let bg := mixedTranscriptBase base b g sign ig
  let bs := mixedTranscriptBase bg b swap effS is
  have flags := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have sg : [b,g,sign].Nodup := by simp [List.nodup_cons]; tauto
  have ss : [b,swap,effS].Nodup := by simp [List.nodup_cons]; tauto
  have ne : effS≠sign := Ne.symm (by tauto)
  have bn : b≠sign := by tauto
  have sn : swap≠sign := by tauto
  have bgS : bg effS=false := by simp only [bg,mixedTranscriptBase,writeBit,Function.update_of_ne ne,hs0]
  have bgB : bg b=base b := by simp only [bg,mixedTranscriptBase,writeBit,Function.update_of_ne bn]
  have bgSwap : bg swap=base swap := by simp only [bg,mixedTranscriptBase,writeBit,Function.update_of_ne sn]
  have bsG : bs sign=mixedTranscriptBit base b g ig := by
    simp only [bs,bg,mixedTranscriptBase,writeBit,Function.update_of_ne (Ne.symm ne),Function.update_self]
  have bsS : bs effS=mixedTranscriptBit base b swap is := by
    simp only [bs,mixedTranscriptBase,writeBit,Function.update_self,mixedTranscriptBit,bgB,bgSwap]
  have ge : Env w bg := env_write w sign ho base _ he
  have se : Env w bs := env_write w effS hoS bg _ ge
  have bd := body_frame w sign effS hn ho hl.swapND bs se X Y
  rw [bsG,bsS] at bd
  have inner := transcriptSelectWindow_pairFrame b swap effS is _ _ ss
    (hl.outside b (by simp)) (hl.outside swap (by simp))
    (hl.outside effS (by simp)) bg bgS (centerWord X) (centerWord Y) _ _ _ bd
  -- The public selection wrapper needs both-word exclusion, supplied by hl.
  exact transcriptSelectWindow_pairFrame b g sign ig _ _ sg
    (hl.outside b (by simp)) (hl.outside g (by simp)) (hl.outside sign (by simp [balancedSharedPorts]))
    base hg0 _ _ _ _ _ inner

def replay (w : Nat → Wire) (b sign effS : Wire) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => cell w b l.1.1 l.1.2 sign effS l.2.1 l.2.2++replay w b sign effS ls

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
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).1)
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).2)) := by
  induction ls generalizing X Y with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons l ls ih =>
    let next := skywalkPayloadCell (mixedTranscriptBit base b l.1.1 l.2.1)
      (mixedTranscriptBit base b l.1.2 l.2.2) (X,Y)
    have c := cell_frame w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hn
      (balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 sign effS (hf l (by simp)) ho)
      (ho sign (by simp)) (ho effS (by simp)) base hg0 hs0 he X Y
    have r := ih (fun q hq => hf q (by simp [hq])) next.1 next.2
    simpa only [replay,mixedTranscriptControls,List.map_cons,skywalkPayloadReplay,next] using c.seq r

/-- Canonical public frame; the original full source value supplies high-zero.
No new mask-clean or ghost-history-zero precondition is introduced. -/
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
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).1.val
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).2.val) := by
  let L := balancedSharedPorts w sign
  let D := balancedSharedBoundary w sign hn
  let next := skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)
  have clean := balancedSharedBoundary_clean w sign base hw hu
  have a := balancedTranscriptCenterPair_frame L D base clean.1 clean.2 X Y
  have r := replay_frame w b sign effS hn ls hf ho base hg0 hs0
    (env_of_canonical_source w hn base original hOriginal hw hu) X Y
  have c := balancedTranscriptCanonicalPair_frame L D base clean.1 clean.2 next.1 next.2
  have result := (a.seq r).seq c
  simpa only [canonicalReplay,L,D,next,balancedSharedPorts_r,balancedSharedPorts_y] using result

theorem replay_counts (w : Nat → Wire) (b sign effS : Wire)
    (_hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) :
    toffoliCount (replay w b sign effS ls)=ls.length*1280 ∧
    measurementCount (replay w b sign effS ls)=ls.length*1025 := by
  induction ls with
  | nil => simp [replay,toffoliCount,measurementCount]
  | cons l ls ih =>
    have hl := balancedSharedTranscriptLayout_direct w b l.1.1 l.1.2 sign effS (hf l (by simp)) ho
    have c := cell_counts w b l.1.1 l.1.2 sign effS l.2.1 l.2.2 hl.swapND
    have r := ih (fun q hq => hf q (by simp [hq]))
    simp only [replay,toffoliCount_append,measurementCount_append,c.1,c.2,r.1,r.2,List.length_cons,Nat.add_mul]
    omega

theorem canonicalReplay_counts (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout w b sign effS ls)
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) :
    toffoliCount (canonicalReplay w b sign effS hn ls)=ls.length*1280+3060 ∧
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
      =ls.length*1280+3060 ∧ _
  rw [t.1,t.2.1,t.2.2.1,t.2.2.2,s.1,s.2.1,s.2.2.1,s.2.2.2,r.1,r.2]
  constructor <;> omega

/-- All 512 rounds use the recorded trace or the exact inactive unit trace. -/
def canonicalTapeReplay (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) : Program :=
  canonicalReplay w b sign effS hn (mixedTranscriptTape w)

theorem canonicalTapeReplay_quotient (w : Nat → Wire) (b sign effS : Wire)
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
    Triple (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base (2*Y).val 0)
      (canonicalTapeReplay w b sign effS hn)
      (PairFrame (wireBlock w 2056 256) (wireBlock w 770 256) base
        (if base b then Y/(x : Fp) else Y).val
        (if base b then Y/(x : Fp) else Y).val) := by
  have r := canonicalReplay_frame w b sign effS hn (mixedTranscriptTape w) hf ho base
    hg0 hs0 hw hu original hOriginal (2*Y) 0
  rw [mixedTranscriptTape_quotient w base b x Y hx0 hx hr] at r
  exact r

theorem canonicalTapeReplay_counts (w : Nat → Wire) (b sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : MixedTranscriptReplayLayout w b sign effS (mixedTranscriptTape w))
    (ho : ∀q∈[b,sign,effS],q∉skywalkSharedWires w) :
    toffoliCount (canonicalTapeReplay w b sign effS hn)=658420 ∧
    measurementCount (canonicalTapeReplay w b sign effS hn)=527860 := by
  have h := canonicalReplay_counts w b sign effS hn (mixedTranscriptTape w) hf ho
  simpa only [mixedTranscriptTape_length,Nat.reduceMul,Nat.reduceAdd] using h

end ECDSAAdd.Arithmetic.OffsetBorrowedCanonical
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedCanonical.canonicalReplay_frame
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedCanonical.replay_counts

#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedCanonical.canonicalTapeReplay_quotient
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedCanonical.canonicalTapeReplay_counts
