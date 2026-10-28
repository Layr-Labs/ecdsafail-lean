import ECDSAAdd.Arithmetic.BalancedInverseSharedReplay
import ECDSAAdd.Arithmetic.BalancedSharedDivisionBridge

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic

/-- Production emission is independent of proof arguments. The concrete
layout certificate is supplied only when proving its semantics/resources. -/
def balancedInverseSharedReplayProgram (w : Nat → Wire) (b effG effS : Wire) : Program :=
  BalancedConvert.center (balancedSharedTargetConvert w)++
  BalancedConvert.center (balancedSharedSourceConvert w)++
  balancedInverseTranscriptReplay (balancedSharedPorts w effG) b effS (mixedTranscriptTape w)++
  BalancedConvert.canonical (balancedSharedTargetConvert w)++
  BalancedConvert.canonical (balancedSharedSourceConvert w)

theorem balancedInverseSharedReplayProgram_eq (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    balancedInverseSharedReplayProgram w b effG effS=
      balancedInverseSharedCanonicalTapeReplay w b effG effS hn := by
  simp only [balancedInverseSharedReplayProgram,balancedInverseSharedCanonicalTapeReplay,
    balancedInverseSharedCanonicalReplay,balancedInverseTranscriptCanonicalReplay,
    balancedTranscriptCenterPair,balancedTranscriptCanonicalPair,balancedSharedBoundary,
    List.append_assoc]

theorem balancedInverseSharedReplayProgram_counts (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : ∀r∈skywalkSharedTape w,MixedTranscriptFieldLayout w b r.1 r.2 effG effS)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) :
    toffoliCount (balancedInverseSharedReplayProgram w b effG effS)=788980 ∧
    measurementCount (balancedInverseSharedReplayProgram w b effG effS)=657908 := by
  rw [balancedInverseSharedReplayProgram_eq w b effG effS hn]
  exact balancedInverseSharedCanonicalTapeReplay_counts w b effG effS hn hf ho

open Secp256k1
/-- Replay on the original 257-bit caller ports. The high sites are
derived zero from the canonical input, even when the caller base has
arbitrary values at those mutable sites. The inverse is independently emitted. -/
theorem balancedInverseSharedMultiplication_replay_frame (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : ∀r∈skywalkSharedTape w,MixedTranscriptFieldLayout w b r.1 r.2 effG effS)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base effG=false) (hs0 : base effS=false)
    (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base Y.val Y.val)
      (balancedInverseSharedReplayProgram w b effG effS)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (2*(if base b then Y*(x : Fp) else Y)).val 0) := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hfirst : (w 0,w 1028)∈skywalkSharedTape w := by
    apply List.mem_map.mpr
    exact ⟨0,by simp,by simp⟩
  have hl := hf _ hfirst
  intro s m h
  have keep (q : Wire) (hq : q∉(skywalkSharedField w).wires) : s.basis q=base q :=
    h.2.2 q (fun hm => hq (by simp [ModInPlaceLayout.wires,hm]))
      (fun hm => hq (by simp [ModInPlaceLayout.wires,hm]))
  have hb := keep b (hl.outside b (by simp))
  have hg := (keep effG (hl.outside effG (by simp))).trans hg0
  have hs := (keep effS (hl.outside effS (by simp))).trans hs0
  have hw := fusedShared_work_clean b effG effS w hl.cell base s.basis _ _ hk h
  have hu' : regValue (skywalkSharedUnused w) s.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hu
    intro q hq
    exact keep q (skywalkShared_unused_outside w hn q hq)
  have ht : skywalkTapeControls s.basis (skywalkSharedTape w)=
      skywalkTapeControls base (skywalkSharedTape w) := by
    apply List.map_congr_left
    intro r hr
    have hlr := hf r hr
    exact Prod.ext (keep r.1 (hlr.outside r.1 (by simp)))
      (keep r.2 (hlr.outside r.2 (by simp)))
  have hz : regValue (wireBlock w 2056 256++[w 2312]) s.basis=Y.val := by
    simpa only [←balancedSharedDivision_z] using h.1
  have ha : regValue (wireBlock w 770 256++[w 1026]) s.basis=Y.val := by
    simpa only [←balancedSharedDivision_a] using h.2.1
  have bound (Z : Fp) : Z.val<2^(wireBlock w 2056 256).length := by
    rw [wireBlock_length]
    exact (ZMod.val_lt Z).trans (by norm_num [p])
  have vr := balancedCanonical_high_zero _ _ s.basis Y.val (bound _) hz
  have vy := balancedCanonical_high_zero _ _ s.basis Y.val (by simpa only [wireBlock_length] using bound Y) ha
  have hin : PairFrame (wireBlock w 2056 256) (wireBlock w 770 256)
      s.basis Y.val Y.val s.basis := ⟨vr.1,vy.1,fun _ _ _ => rfl⟩
  have replay := balancedInverseSharedCanonicalTapeReplay_product w b effG effS hn hf ho
    s.basis hg hs hw hu' x Y hx0 hx (ht.trans hr)
  rw [←balancedInverseSharedReplayProgram_eq w b effG effS hn] at replay
  obtain ⟨phase,out⟩ := replay s m hin
  rw [hb] at out
  have away := balancedSharedDivision_high_outside w hn
  have wide := balancedPair_widen _ _ _ _ s.basis _ _ _ out away.1 away.2 vr.2 vy.2
  rw [←balancedSharedDivision_z,←balancedSharedDivision_a] at wide
  exact ⟨phase,wide.1,wide.2.1,fun q hz ha =>
    (wide.2.2 q hz ha).trans (h.2.2 q hz ha)⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.balancedInverseSharedReplayProgram_eq
#print axioms ECDSAAdd.Arithmetic.balancedInverseSharedReplayProgram_counts
#print axioms ECDSAAdd.Arithmetic.balancedInverseSharedMultiplication_replay_frame
