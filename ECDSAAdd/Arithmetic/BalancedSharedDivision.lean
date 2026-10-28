import ECDSAAdd.Arithmetic.BalancedSharedDivisionBridge
import ECDSAAdd.Arithmetic.BorrowedSkywalkUnaryFrames

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- Exact Stage 2 field division: the original doubling and XOR clear
surround the concrete balanced replay emission. -/
def balancedSharedFieldDivision (w : Nat → Wire) (b effG effS : Wire) : Program :=
  dblInPlace (borrowedSkywalkUnary w) p ++
  balancedSharedReplayProgram w b effG effS ++
  copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a

theorem balancedSharedFieldDivision_spec (w : Nat → Wire) (b effG effS : Wire)
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
      (balancedSharedFieldDivision w b effG effS)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (if base b then Y/(x : Fp) else Y).val 0) := by
  have hfirst : (w 0,w 1028)∈skywalkSharedTape w := by
    apply List.mem_map.mpr
    exact ⟨0,by simp,by simp⟩
  have hl := hf _ hfirst
  have h1 := borrowedSkywalkUnary_double_frame w hn base hk hu Y 0
  have h2 := balancedSharedDivision_replay_frame w b effG effS hn hf ho base
    hg0 hs0 hk hu x Y hx0 hx hr
  have h3 := retained_copy_frame b effG effS w hl.cell base
    (if base b then Y/(x : Fp) else Y).val (if base b then Y/(x : Fp) else Y).val
  simp only [Nat.xor_self] at h3
  simpa only [balancedSharedFieldDivision,List.append_assoc,ZMod.val_zero]
    using (h1.seq h2).seq h3

theorem balancedSharedFieldDivision_counts (w : Nat → Wire) (b effG effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hf : ∀r∈skywalkSharedTape w,MixedTranscriptFieldLayout w b r.1 r.2 effG effS)
    (ho : ∀q∈[b,effG,effS],q∉skywalkSharedWires w) :
    toffoliCount (balancedSharedFieldDivision w b effG effS)=789491 ∧
    measurementCount (balancedSharedFieldDivision w b effG effS)=658419 := by
  have hw := skywalkShared_field_widths w
  have hd := modUnary_counts (borrowedSkywalkUnary w) 256 p
    (borrowedSkywalkUnary_widths w) (by omega)
  have hr := balancedSharedReplayProgram_counts w b effG effS hn hf ho
  have hlen : (skywalkSharedField w).z.length=(skywalkSharedField w).a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hc := copyRegister_counts none (skywalkSharedField w).z (skywalkSharedField w).a hlen
  simp only [balancedSharedFieldDivision,toffoliCount_append,measurementCount_append,
    hd.1,hd.2.1,hr.1,hr.2,hc.1,hc.2]
  norm_num

end ECDSAAdd.Arithmetic

#print axioms ECDSAAdd.Arithmetic.balancedSharedFieldDivision_spec
#print axioms ECDSAAdd.Arithmetic.balancedSharedFieldDivision_counts
#print axioms ECDSAAdd.Arithmetic.balancedSharedFieldDivision
