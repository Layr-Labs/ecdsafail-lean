import ECDSAAdd.Arithmetic.BalancedInverseSharedMultiplicationReplay
import ECDSAAdd.Arithmetic.BorrowedSkywalkUnaryFrames

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic
open Secp256k1

def balancedInverseSharedFieldMultiplication (w : Nat → Wire) (b effG effS : Wire) : Program :=
  copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a ++
  balancedInverseSharedReplayProgram w b effG effS ++
  halfInPlace (borrowedSkywalkUnary w) p

theorem balancedInverseSharedFieldMultiplication_spec (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : ∀r∈skywalkSharedTape w,MixedTranscriptFieldLayout w b r.1 r.2 effG effS)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w)
    (base : BasisState) (hg0 : base effG=false) (hs0 : base effS=false)
    (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base Y.val 0)
      (balancedInverseSharedFieldMultiplication w b effG effS)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (if base b then Y*(x : Fp) else Y).val 0) := by
  have hfirst : (w 0,w 1028)∈skywalkSharedTape w := by
    apply List.mem_map.mpr
    exact ⟨0,by simp,by simp⟩
  have hl := hf _ hfirst
  have h1 := retained_copy_frame b effG effS w hl.cell base Y.val 0
  simp only [Nat.zero_xor] at h1
  have h2 := balancedInverseSharedMultiplication_replay_frame w b effG effS hn hf ho
    base hg0 hs0 hk hu x Y hx0 hx hr
  have h3 := borrowedSkywalkUnary_half_frame w hn base hk hu
    (2*(if base b then Y*(x : Fp) else Y)) 0
  have ht2 : (2 : Fp)≠0 := by decide
  have he : (2*(if base b then Y*(x : Fp) else Y))/2=
      (if base b then Y*(x : Fp) else Y) := by field_simp [ht2]
  rw [he] at h3
  simpa only [balancedInverseSharedFieldMultiplication,List.append_assoc,ZMod.val_zero]
    using (h1.seq h2).seq h3

theorem balancedInverseSharedFieldMultiplication_counts (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : ∀r∈skywalkSharedTape w,MixedTranscriptFieldLayout w b r.1 r.2 effG effS)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) :
    toffoliCount (balancedInverseSharedFieldMultiplication w b effG effS)=789492 ∧
    measurementCount (balancedInverseSharedFieldMultiplication w b effG effS)=658420 := by
  have hw := skywalkShared_field_widths w
  have hu := modUnary_counts (borrowedSkywalkUnary w) 256 p
    (borrowedSkywalkUnary_widths w) (by omega)
  have hr := balancedInverseSharedReplayProgram_counts w b effG effS hn hf ho
  have hlen : (skywalkSharedField w).z.length=(skywalkSharedField w).a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hc := copyRegister_counts none (skywalkSharedField w).z (skywalkSharedField w).a hlen
  simp only [balancedInverseSharedFieldMultiplication,toffoliCount_append,measurementCount_append,
    hu.2.2.1,hu.2.2.2,hr.1,hr.2,hc.1,hc.2]
  norm_num

end ECDSAAdd.Arithmetic

#print axioms ECDSAAdd.Arithmetic.balancedInverseSharedFieldMultiplication_spec
#print axioms ECDSAAdd.Arithmetic.balancedInverseSharedFieldMultiplication_counts

#print axioms ECDSAAdd.Arithmetic.balancedInverseSharedFieldMultiplication
