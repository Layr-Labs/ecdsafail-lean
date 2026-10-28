import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalReplay
import ECDSAAdd.Arithmetic.OffsetBorrowedSharedEmission
import ECDSAAdd.Arithmetic.BalancedSharedDivisionBridge
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic
open Secp256k1
attribute [local irreducible] run

/-- Replay on the original 257-bit caller ports. The high sites are
derived zero from the canonical input, even when the caller base has
arbitrary values at those mutable sites. -/
theorem offsetBorrowedSharedDivision_replay_frame (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : ∀r∈skywalkSharedTape w,MixedTranscriptFieldLayout w b r.1 r.2 effG effS)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) (base : BasisState)
    (hg0 : base effG=false) (hs0 : base effS=false)
    (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base (2*Y).val 0)
      (offsetBorrowedSharedReplayProgram w b effG effS)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (if base b then Y/(x : Fp) else Y).val
        (if base b then Y/(x : Fp) else Y).val) := by
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
  have hz : regValue (wireBlock w 2056 256++[w 2312]) s.basis=(2*Y).val := by
    simpa only [←balancedSharedDivision_z] using h.1
  have ha : regValue (wireBlock w 770 256++[w 1026]) s.basis=0 := by
    simpa only [←balancedSharedDivision_a] using h.2.1
  have bound (Z : Fp) : Z.val<2^(wireBlock w 2056 256).length := by
    rw [wireBlock_length]
    exact (ZMod.val_lt Z).trans (by norm_num [p])
  have vr := balancedCanonical_high_zero _ _ s.basis (2*Y).val (bound _) hz
  have vy := balancedCanonical_high_zero _ _ s.basis 0 (by simp [wireBlock_length]) ha
  have hin : PairFrame (wireBlock w 2056 256) (wireBlock w 770 256)
      s.basis (2*Y).val 0 s.basis := ⟨vr.1,vy.1,fun _ _ _ => rfl⟩
  have replay := OffsetBorrowedCanonical.canonicalTapeReplay_quotient w b effG effS hn
    (mixedTranscriptTape_layout w b effG effS hf) ho
    s.basis hg hs hw hu' (0 : Fp) (by simpa using h.2.1) x Y hx0 hx (ht.trans hr)
  rw [←offsetBorrowedSharedReplayProgram_eq w b effG effS hn] at replay
  obtain ⟨phase,out⟩ := replay s m hin
  rw [hb] at out
  have away := balancedSharedDivision_high_outside w hn
  have wide := balancedPair_widen _ _ _ _ s.basis _ _ _ out away.1 away.2 vr.2 vy.2
  rw [←balancedSharedDivision_z,←balancedSharedDivision_a] at wide
  exact ⟨phase,wide.1,wide.2.1,fun q hz ha =>
    (wide.2.2 q hz ha).trans (h.2.2 q hz ha)⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.offsetBorrowedSharedDivision_replay_frame
