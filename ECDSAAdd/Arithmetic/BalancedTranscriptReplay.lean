import ECDSAAdd.Arithmetic.BalancedTranscriptCell
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic
open Secp256k1 BalancedField

private theorem selected_reg (base : BasisState) (b source flag : Wire) (v : Bool)
    (r : List Wire) (hf : flag∉r) :
    regValue r (mixedTranscriptBase base b source flag v)=regValue r base := by
  apply regValue_congr
  intro q hq
  simp [mixedTranscriptBase,writeBit,Function.update,show q≠flag from fun e => hf (e ▸ hq)]

private theorem selected_other (base : BasisState) (b source flag q : Wire) (v : Bool)
    (hne : q≠flag) : mixedTranscriptBase base b source flag v q=base q := by
  simp [mixedTranscriptBase,writeBit,Function.update,hne]

/-- Exact mixed selection around the physically emitted centered kernel. -/
theorem balancedTranscriptCell_frame (L : BalancedCircuit.Layout)
    (b g swap effS : Wire) (inactiveG inactiveS : Bool)
    (hl : BalancedTranscriptLayout L b g swap effS) (base : BasisState)
    (hg0 : base L.sign=false) (hs0 : base effS=false)
    (hc : ∀q∈BalancedCircuit.work L,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base (centerWord X) (centerWord Y))
      (balancedTranscriptCell L b g swap effS inactiveG inactiveS)
      (PairFrame L.r L.y base
        (centerWord (skywalkPayloadCell (mixedTranscriptBit base b g inactiveG)
          (mixedTranscriptBit base b swap inactiveS) (X,Y)).1)
        (centerWord (skywalkPayloadCell (mixedTranscriptBit base b g inactiveG)
          (mixedTranscriptBit base b swap inactiveS) (X,Y)).2)) := by
  let bg := mixedTranscriptBase base b g L.sign inactiveG
  let bs := mixedTranscriptBase bg b swap effS inactiveS
  have sg : [b,g,L.sign].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hl.controls q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  have ss : [b,swap,effS].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hl.controls q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  have d0 := List.nodup_cons.mp hl.controls
  have d1 := List.nodup_cons.mp d0.2
  have d2 := List.nodup_cons.mp d1.2
  have d3 := List.nodup_cons.mp d2.2
  have ne : effS≠L.sign := Ne.symm (by simpa using d3.1)
  have bn : b≠L.sign := by
    have h := (List.nodup_cons.mp sg).1
    intro e; exact h (by simp [e])
  have sn : swap≠L.sign := by
    intro e
    exact d2.1 (by simp [e])
  have bgS : bg effS=false := (selected_other _ _ _ _ _ _ ne).trans hs0
  have bgB : bg b=base b := selected_other _ _ _ _ _ _ bn
  have bgSwap : bg swap=base swap := selected_other _ _ _ _ _ _ sn
  have bsG : bs L.sign=mixedTranscriptBit base b g inactiveG := by
    rw [show bs L.sign=bg L.sign from selected_other _ _ _ _ _ _ (Ne.symm ne)]
    simp [bg,mixedTranscriptBase,writeBit]
  have bsS : bs effS=mixedTranscriptBit base b swap inactiveS := by
    simp [bs,mixedTranscriptBase,mixedTranscriptBit,writeBit,bgB,bgSwap]
  have clean : ∀q∈BalancedCircuit.work L,bs q=false := by
    intro q hq
    have qg : q≠L.sign := fun e => hl.scratch.1 (e ▸ hq)
    have qs : q≠effS := fun e => hl.scratch.2 (e ▸ hq)
    exact (selected_other _ _ _ _ _ _ qs).trans
      ((selected_other _ _ _ _ _ _ qg).trans (hc q hq))
  have body := balancedTranscriptBody_frame L effS hl.widths hl.kernel hl.swapND bs clean X Y
  rw [bsG,bsS] at body
  have inner := transcriptSelectWindow_pairFrame b swap effS inactiveS L.r L.y ss
    (hl.outside b (by simp)) (hl.outside swap (by simp))
    (hl.outside effS (by simp)) bg bgS (centerWord X) (centerWord Y) _ _ _ body
  exact transcriptSelectWindow_pairFrame b g L.sign inactiveG L.r L.y sg
    (hl.outside b (by simp)) (hl.outside g (by simp))
    (hl.outside L.sign (by simp)) base hg0 _ _ _ _ _ inner

def balancedTranscriptReplay (L : BalancedCircuit.Layout) (b effS : Wire) :
    List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => balancedTranscriptCell L b l.1.1 l.1.2 effS l.2.1 l.2.2 ++
    balancedTranscriptReplay L b effS ls

def BalancedTranscriptReplayLayout (L : BalancedCircuit.Layout) (b effS : Wire)
    (ls : List MixedTranscriptLetter) : Prop :=
  ∀l∈ls,BalancedTranscriptLayout L b l.1.1 l.1.2 effS

/-- Every round has a full pair frame, including all quantum transcript controls. -/
theorem balancedTranscriptReplay_frame (L : BalancedCircuit.Layout) (b effS : Wire)
    (ls : List MixedTranscriptLetter) (hl : BalancedTranscriptReplayLayout L b effS ls)
    (base : BasisState) (hg0 : base L.sign=false) (hs0 : base effS=false)
    (hc : ∀q∈BalancedCircuit.work L,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base (centerWord X) (centerWord Y))
      (balancedTranscriptReplay L b effS ls)
      (PairFrame L.r L.y base
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).1)
        (centerWord (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).2)) := by
  induction ls generalizing X Y with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons l ls ih =>
    let Q := skywalkPayloadCell (mixedTranscriptBit base b l.1.1 l.2.1)
      (mixedTranscriptBit base b l.1.2 l.2.2) (X,Y)
    have h1 := balancedTranscriptCell_frame L b l.1.1 l.1.2 effS l.2.1 l.2.2
      (hl l (by simp)) base hg0 hs0 hc X Y
    have h2 := ih (fun q hq => hl q (by simp [hq])) Q.1 Q.2
    simpa only [balancedTranscriptReplay,mixedTranscriptControls,List.map_cons,
      skywalkPayloadReplay,Q] using h1.seq h2

theorem balancedTranscriptCell_counts (L : BalancedCircuit.Layout)
    (b g swap effS : Wire) (ig is : Bool) (hw : L.Widths)
    (hs : (effS::L.r++L.y).Nodup) :
    toffoliCount (balancedTranscriptCell L b g swap effS ig is)=1535 ∧
    measurementCount (balancedTranscriptCell L b g swap effS ig is)=1279 := by
  have w := BalancedCleanup.widths L.toLayout hw
  have sw := swapRegisters_resources effS L.r L.y (w.2.1.trans w.2.2.1.symm) hs
  have k := BalancedCircuit.counts L hw
  have si := transcriptSelectWindow_counts b swap effS is (balancedTranscriptBody L effS)
  have so := transcriptSelectWindow_counts b g L.sign ig
    (transcriptSelectWindow b swap effS is (balancedTranscriptBody L effS))
  simp only [balancedTranscriptCell,so.1,so.2,si.1,si.2]
  simp only [balancedTranscriptBody,toffoliCount_append,measurementCount_append,
    k.1,k.2,sw.1,sw.2.1,w.2.1]
  norm_num [toffoliCount,measurementCount]

theorem balancedTranscriptReplay_counts (L : BalancedCircuit.Layout) (b effS : Wire)
    (ls : List MixedTranscriptLetter) (hl : BalancedTranscriptReplayLayout L b effS ls) :
    toffoliCount (balancedTranscriptReplay L b effS ls)=ls.length*1535 ∧
    measurementCount (balancedTranscriptReplay L b effS ls)=ls.length*1279 := by
  induction ls with
  | nil => simp [balancedTranscriptReplay,toffoliCount,measurementCount]
  | cons l ls ih =>
    have h := hl l (by simp)
    have c := balancedTranscriptCell_counts L b l.1.1 l.1.2 effS l.2.1 l.2.2 h.widths h.swapND
    have i := ih (fun q hq => hl q (by simp [hq]))
    simp only [balancedTranscriptReplay,toffoliCount_append,measurementCount_append,
      c.1,c.2,i.1,i.2,List.length_cons,Nat.add_mul]
    omega
end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.balancedTranscriptCell_frame
#print axioms ECDSAAdd.Arithmetic.balancedTranscriptReplay_frame
#print axioms ECDSAAdd.Arithmetic.balancedTranscriptReplay_counts
