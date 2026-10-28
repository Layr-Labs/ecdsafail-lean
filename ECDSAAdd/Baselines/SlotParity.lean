import ECDSAAdd.Baselines.SlotBalanced

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem parityHeads_gateSlots_le (b : MappedBit) (a y cc cb c d : Wire) :
    gateSlots (BalancedCleanupOffset.prepareHead b a y cc cb c d) ≤ 18 ∧
    gateSlots (BalancedCleanupOffset.releaseHead b a y cc cb c d) ≤ 14 := by
  have h := mappedBit_gateSlots_le b y cc c
  simp only [BalancedCleanupOffset.prepareHead,BalancedCleanupOffset.releaseHead,
    gateSlots_append,majority_gateSlots,eraseCarry_gateSlots,gateSlots_cons,
    gateSlots_nil,instructionSlots]; omega

theorem parityChain_gateSlots_le (bs : List MappedBit) (xs ys cs ds : List Wire) (cc cb t : Wire) :
    gateSlots (TerminalParityMeasure.chain bs xs ys cs ds cc cb t) ≤ 40*bs.length+2 := by
  induction bs,xs,ys,cs,ds,cc,cb,t using TerminalParityMeasure.chain.induct with
  | case1 b a y c d cc cb t =>
    have h := (mappedBit_gateSlots_le b y cc c).2.2
    simp only [TerminalParityMeasure.chain,TerminalParityMeasure.leaf,TerminalParityMeasure.program,
      gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots,eraseCarry_gateSlots,List.length_singleton]; omega
  | case2 b bs a xs y ys c cs d ds cc cb t hcond ih =>
    have h := parityHeads_gateSlots_le b a y cc cb c d
    simp only [TerminalParityMeasure.chain,gateSlots_append,List.length_cons] at *
    omega
  | case3 cc cb t => simp [TerminalParityMeasure.chain,flipBelow,gateSlots_cons,instructionSlots]
  | case4 bs xs ys cs ds cc cb t h => simp [TerminalParityMeasure.chain]

theorem slimChain_gateSlots_le (bs : List MappedBit) (xs ys cs ds : List Wire) (cc cb t : Wire) :
    gateSlots (BalancedCleanupOffsetSlim.chain bs xs ys cs ds cc cb t) ≤ 40*bs.length+2 := by
  induction bs,xs,ys,cs,ds,cc,cb,t using BalancedCleanupOffsetSlim.chain.induct with
  | case1 b a y c d cc cb t =>
    have h := (mappedBit_gateSlots_le b y cc c).2.2
    have hc := compareChain_gateSlots_le none [a] [y] [d] cb t
    simp only [List.length_singleton] at hc
    simp only [BalancedCleanupOffsetSlim.chain,gateSlots_append,gateSlots_cons,
      gateSlots_nil,instructionSlots,List.length_singleton]; omega
  | case2 b bs a xs y ys c cs d ds cc cb t hcond ih =>
    have h := parityHeads_gateSlots_le b a y cc cb c d
    simp only [BalancedCleanupOffsetSlim.chain,gateSlots_append,List.length_cons] at *
    omega
  | case3 cc cb t => simp [BalancedCleanupOffsetSlim.chain,flipBelow,gateSlots_cons,instructionSlots]
  | case4 bs xs ys cs ds cc cb t h => simp [BalancedCleanupOffsetSlim.chain]

theorem offsetFront_gateSlots_le (L : BalancedCleanupOffset.Layout) (hw : L.Widths) :
    gateSlots (BalancedCleanupOffset.front L) ≤ 1600 := by
  have hl := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have hr := rotate_gateSlots_le L.r
  have hx : L.r.length = 256 := hl.2.1
  have hy : L.y.length = 256 := hl.2.2.1
  rw [hx] at hr
  simp only [BalancedCleanupOffset.front,BalancedCleanup.prepareSign,BalancedCleanupOffset.view,
    gateSlots_append,signComplement_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots]
  change 1 + L.r.length + (gateSlots (rotateLeft L.r) + 3 + L.y.length + L.y.length + 1) + 1 ≤ _
  omega

theorem offsetParity_gateSlots_le (L : BalancedCleanupOffset.Layout) (hw : L.Widths) :
    gateSlots (TerminalParityOffset.program L) ≤ 14000 ∧
    gateSlots (BalancedCleanupOffsetZero.program L) ≤ 14000 := by
  have hf := offsetFront_gateSlots_le L hw
  have h1 := parityChain_gateSlots_le (BalancedCleanupOffset.offsetBits L).tail L.y.tail L.r.tail
    L.offsetCarry.tail L.carry.tail L.one (L.carry.headD 0) L.parity
  have h2 := slimChain_gateSlots_le (BalancedCleanupOffset.offsetBits L).tail L.y.tail L.r.tail
    L.offsetCarry.tail L.carry.tail L.one (L.carry.headD 0) L.parity
  simp only [List.length_tail,BalancedCleanupOffset.offsetBits_length] at h1 h2
  simp only [TerminalParityOffset.program,TerminalParityOffset.core,TerminalParityZeroHead.program,
    BalancedCleanupOffsetZero.program,BalancedCleanupOffsetZero.core,BalancedCleanupOffsetZeroHead.program,
    gateSlots_append,reverse_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots,
    majority_gateSlots,eraseCarry_gateSlots]
  omega

end ECDSAAdd.Baselines
