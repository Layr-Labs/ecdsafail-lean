import ECDSAAdd.Baselines.SlotMapped

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem rotate_gateSlots_le (xs : List Wire) :
    gateSlots (rotateRight xs) ≤ 3*xs.length ∧ gateSlots (rotateLeft xs) ≤ 3*xs.length := by
  induction xs using List.twoStepInduction with
  | nil => simp [rotateRight,rotateLeft]
  | singleton x => simp [rotateRight,rotateLeft]
  | cons_cons x y xs ih ih' =>
    have ht := ih' y
    simp only [rotateRight,rotateLeft,gateSlots_append,swapBits,gateSlots_cons,
      gateSlots_nil,instructionSlots,List.length_cons] at *
    omega

theorem knownXor_gateSlots_le (b : MappedBit) (t : Wire) :
    gateSlots (KnownOutputAdder.xorBit b t) ≤ 2 := by
  cases b with
  | mk w f => cases w <;> cases f <;>
      simp [KnownOutputAdder.xorBit,gateSlots_cons,instructionSlots]

theorem knownAdder_gateSlots_le (xs ds : List MappedBit) (ys cs : List Wire) (c : Wire) :
    gateSlots (KnownOutputAdder.program xs ys ds cs c) ≤ 14*xs.length := by
  induction xs, ys, ds, cs, c using KnownOutputAdder.program.induct with
  | case1 b b' bs y y' ys d d' ds t ts c ih =>
    have h := mappedBit_gateSlots_le b y c t
    have h1 := knownXor_gateSlots_le b' t
    have h2 := knownXor_gateSlots_le d' t
    simp only [KnownOutputAdder.program,KnownOutputAdder.prepare,gateSlots_append,
      gateSlots_cons,gateSlots_nil,instructionSlots,List.length_cons] at *
    omega
  | case2 b y d cs c =>
    have h := (mappedBit_gateSlots_le b y c c).2.2
    simpa only [KnownOutputAdder.program,List.length_singleton] using h.trans (by decide : 3 ≤ 14)
  | case3 xs ys ds cs c h => simp [KnownOutputAdder.program]

theorem nativeFirst_gateSlots_le (w : Nat → Wire) :
    gateSlots (NativeFirstDirect.forward w) ≤ 10000 ∧
    gateSlots (NativeFirstKnown.inverse w) ≤ 10000 := by
  have hh := mappedAdd_gateSlots_le (NativeFirstDirect.hBits w false)
    (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797)
  have hk (b : Bool) := mappedAdd_gateSlots_le (NativeFirstDirect.kBits w b)
    (wireBlock w 771 257) (wireBlock w 1540 256) (w 770)
  have hr := rotate_gateSlots_le (wireBlock w 770 258)
  have hn := knownAdder_gateSlots_le (NativeFirstDirect.hBits w true) (NativeFirstKnown.desired w)
    (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797)
  simp only [NativeFirstDirect.hBits_length,NativeFirstDirect.kBits_length,wireBlock_length] at hh hk hn hr
  have hkf := hk false
  have hkt := hk true
  simp only [NativeFirstDirect.forward,NativeFirstKnown.inverse,NativeFirstKnown.hReceiver,
    sealedProgram_eq,NativeFirstDirect.hAdd,NativeFirstDirect.kAdd,NativeFirstDirect.lowCopy,
    NativeFirstDirect.inverseUnmiddle,NativeFirstDirect.inverseBack,gateSlots_append,
    copyRegister_gateSlots,wireBlock_length,gateSlots_cons,gateSlots_nil,instructionSlots]
  omega

end ECDSAAdd.Baselines
