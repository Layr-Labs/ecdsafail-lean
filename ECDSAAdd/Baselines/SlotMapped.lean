import ECDSAAdd.Baselines.SlotAlgebra

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

@[simp] theorem rename_gateSlots (f : Wire → Wire) (p : Program) :
    gateSlots (renameProgram f p) = gateSlots p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simpa only [renameProgram, List.map_cons, renameInstr, gateSlots_cons,
      instructionSlots, List.length_map] using congrArg (_ + ·) ih

theorem mappedBit_gateSlots_le (b : MappedBit) (y c t : Wire) :
    gateSlots (mappedMajority b y c t) ≤ 8 ∧
    gateSlots (mappedEraseCarry b y c t) ≤ 6 ∧
    gateSlots (mappedSum b y c) ≤ 3 := by
  cases b with
  | mk w f => cases w <;> cases f <;>
      simp [mappedMajority, mappedEraseCarry, mappedSum, borrowMajority, eraseBorrow,
        gateSlots_cons, instructionSlots]

theorem mappedAdd_gateSlots_le (xs : List MappedBit) (ys cs : List Wire) (c : Wire) :
    gateSlots (mappedAdd xs ys cs c) ≤ 17*xs.length := by
  induction xs, ys, cs, c using mappedAdd.induct with
  | case1 b b' bs y y' ys d ds c ih =>
    simp only [List.length_cons] at ih
    have h := mappedBit_gateSlots_le b y c d
    simp only [mappedAdd, gateSlots_append, List.length_cons]
    omega
  | case2 b y cs c =>
    have h := (mappedBit_gateSlots_le b y c c).2.2
    simpa only [mappedAdd, List.length_singleton] using h.trans (by decide : 3 ≤ 17)
  | case3 xs ys cs c h => simp [mappedAdd]

theorem mappedConst_gateSlots_le (ctrl : Option Wire) (ys cs : List Wire) (c k : Nat) :
    gateSlots (mappedConstAdd ctrl ys cs c k) ≤ 17*ys.length := by
  simpa only [mappedConstAdd, mappedConstant_length] using
    mappedAdd_gateSlots_le (mappedConstant ctrl ys.length k) ys cs c

theorem eraseLt_gateSlots_le (xs ys cs : List Wire) (c t : Wire) :
    gateSlots (eraseLtChain xs ys cs c t) ≤ 14*xs.length := by
  induction xs, ys, cs, c, t using eraseLtChain.induct with
  | case1 a a' as b b' bs d ds c t ih =>
    simp only [List.length_cons] at ih
    simp only [eraseLtChain, gateSlots_append, borrowMajority, eraseBorrow, majority_gateSlots,
      eraseCarry_gateSlots, gateSlots_cons, gateSlots_nil, instructionSlots, List.length_cons]
    omega
  | case2 a b cs c t => simp [eraseLtChain, eraseBorrow, gateSlots_cons, instructionSlots]
  | case3 xs ys cs c t h => simp [eraseLtChain]

theorem compareConstant_gateSlots_le (xs cs : List Wire) (c t k : Nat) :
    gateSlots (compareConstantLt xs cs c t k) ≤ 18*xs.length := by
  induction xs, cs, c, t, k using compareConstantLt.induct with
  | case1 x x' xs d ds c t k ih =>
    have h := mappedBit_gateSlots_le {wire:=none,flip:=decide (k%2=1)} x c d
    simp only [List.length_cons] at ih
    simp only [compareConstantLt, constantBorrow, constantBorrowErase, gateSlots_append,
      gateSlots_cons, gateSlots_nil, instructionSlots, List.length_cons]
    omega
  | case2 x cs c t k =>
    have h := (mappedBit_gateSlots_le {wire:=none,flip:=decide (k%2=1)} x c t).1
    simp only [compareConstantLt, constantBorrow, gateSlots_append,
      gateSlots_cons, gateSlots_nil, instructionSlots, List.length_cons, List.length_nil]
    omega
  | case3 xs cs c t k h => simp [compareConstantLt]

theorem canonicalMod_gateSlots_le (L : MeasuredCanonicalModLayout) (n c p : Nat) (hw : L.Widths n) :
    gateSlots (L.program c p) ≤ 66*n+37 := by
  have he : L.extended.length = n+1 := by simp [MeasuredCanonicalModLayout.extended, hw.out]
  have hs := mappedAdd_gateSlots_le (mappedRead L.src false++[{wire:=none,flip:=false}]) L.extended L.carry L.cin
  simp only [List.length_append, List.length_cons, List.length_nil, mappedRead_length, hw.src] at hs
  have hc := compareConstant_gateSlots_le L.out (L.carry.take (L.out.length-1)) L.cin L.flag p
  have hm := mappedConst_gateSlots_le (some L.flag) L.extended L.carry L.cin c
  have hb := eraseLt_gateSlots_le L.out L.src (L.carry.take (L.out.length-1)) L.cin L.flag
  rw [hw.out] at hc hb
  rw [he] at hm
  simp only [MeasuredCanonicalModLayout.program, MeasuredCanonicalModLayout.sum,
    compareConstantGe, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots, hw.out]
  omega

end ECDSAAdd.Baselines
