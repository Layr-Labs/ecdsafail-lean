import ECDSAAdd.Baselines.SlotNativeFirst
import ECDSAAdd.Baselines.SlotSignedInteger
import ECDSAAdd.Baselines.SlotSignedSquare

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem literalCells_gateSlots_le (b : Bool) (x c t one : Wire) :
    gateSlots (literalConstStep b x c t) ≤ 6 ∧
    gateSlots (literalConstErase b x c t one) ≤ 6 ∧
    gateSlots (literalConstSum b x c) ≤ 2 := by
  cases b <;> simp [literalConstStep,literalConstSum,literalConstCarry,literalConstErase,
    gateSlots_cons,instructionSlots]

theorem literalAdd_gateSlots_le (xs cs : List Wire) (c one k : Nat) :
    gateSlots (literalConstAdd xs cs c one k) ≤ 12*xs.length := by
  induction xs, cs, c, one, k using literalConstAdd.induct with
  | case1 x x' xs d ds c one k ih =>
    have h := literalCells_gateSlots_le (decide (k%2=1)) x c d one
    simp only [literalConstAdd,gateSlots_append,List.length_cons] at *; omega
  | case2 x cs c one k =>
    have h := (literalCells_gateSlots_le (decide (k%2=1)) x c c one).2.2
    simpa only [literalConstAdd,List.length_singleton] using h.trans (by decide : 2 ≤ 12)
  | case3 xs cs c one k h => simp [literalConstAdd]

theorem mappedSub_gateSlots_le (xs : List MappedBit) (ys cs : List Wire) (c : Wire) :
    gateSlots (mappedSub xs ys cs c) ≤ 17*xs.length+2*ys.length := by
  have h := mappedAdd_gateSlots_le xs ys cs c
  simp only [mappedSub,gateSlots_append,notRegister_gateSlots]; omega

theorem balancedConvert_gateSlots_le (L : BalancedConvert.Layout) (hw : L.Widths) :
    gateSlots (BalancedConvert.center L) ≤ 12000 ∧
    gateSlots (BalancedConvert.canonical L) ≤ 12000 := by
  have hl : L.word.length = 256 := by simp [BalancedConvert.Layout.word,hw.1]
  have hc : (BalancedConvert.correction L).length = 256 := by simp [BalancedConvert.correction]
  have a := literalAdd_gateSlots_le L.word L.carry L.cin L.one BalancedConvert.bias
  have b := literalAdd_gateSlots_le L.word L.carry L.cin L.one BalancedConvert.inverseBias
  have c := mappedAdd_gateSlots_le (BalancedConvert.correction L) L.word L.carry L.cin
  have d := mappedSub_gateSlots_le (BalancedConvert.correction L) L.word L.carry L.cin
  rw [hl] at a b
  rw [hc] at c
  rw [hc,hl] at d
  simp only [BalancedConvert.center,BalancedConvert.canonical,BalancedConvert.predicate,
    gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots]; omega

theorem balancedCore_gateSlots_le (L : BalancedCircuit.Layout) (hw : L.Widths) :
    gateSlots (BalancedCircuit.coreProgram L) ≤ 10000 ∧
    gateSlots (OffsetBorrowedInverse.tail L) ≤ 11000 := by
  have hl := BalancedCleanup.widths L.toLayout hw
  have hs : (BalancedCircuit.rawSource L).length = 257 := by
    simp only [BalancedCircuit.rawSource,List.length_append,List.length_singleton,hl.2.2.1]
  have ht : (BalancedCircuit.rawTarget L).length = 257 := by
    simp only [BalancedCircuit.rawTarget,List.length_append,List.length_singleton,hl.2.1]
  have hf : (BalancedCircuit.foldTarget L++[L.cout]).length = 257 := by
    simp only [BalancedCircuit.foldTarget,List.length_append,List.length_cons,List.length_nil,hw.1]
  have hb : (BalancedCircuit.foldBits L).length = 257 := by simp [BalancedCircuit.foldBits]
  have a := addInPlace_gateSlots_le (BalancedCircuit.rawSource L) (BalancedCircuit.rawTarget L) L.carry L.sign
  have b := subInPlace_gateSlots_le (BalancedCircuit.rawSource L) (BalancedCircuit.rawTarget L) L.carry L.sign
  have c := mappedAdd_gateSlots_le (BalancedCircuit.foldBits L) (BalancedCircuit.foldTarget L++[L.cout]) L.carry L.parity
  have d := mappedSub_gateSlots_le (BalancedCircuit.foldBits L) (BalancedCircuit.foldTarget L++[L.cout]) L.carry L.parity
  have r := rotate_gateSlots_le (BalancedCircuit.rawTarget L)
  rw [hs] at a
  rw [hs,ht] at b
  rw [hb] at c
  rw [hb,hf] at d
  rw [ht] at r
  simp only [BalancedCircuit.coreProgram,OffsetBorrowedInverse.tail,
    BalancedCircuit.seedViews,BalancedCircuit.rawAdd,BalancedCircuit.prepareFold,
    BalancedCircuit.fold,BalancedCircuit.releaseSelectors,BalancedInverse.recoverSelectors,
    BalancedInverse.undoFold,BalancedInverse.undoPreparation,BalancedInverse.rawSubtract,
    gateSlots_append,reverse_gateSlots,signComplement_gateSlots,hs,
    gateSlots_cons,gateSlots_nil,instructionSlots,List.length_cons,List.length_nil]
  omega

end ECDSAAdd.Baselines
