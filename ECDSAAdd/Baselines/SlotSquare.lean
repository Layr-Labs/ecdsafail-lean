import ECDSAAdd.Baselines.SlotModular

namespace ECDSAAdd.Baselines
open Arithmetic Challenge

theorem squareRow_gateSlots_le (sub : Bool) (c : Wire) (xs pad mask dst carry : List Wire) (cin : Wire) :
    gateSlots (squareRow sub c xs pad mask dst carry cin) ≤ 15*mask.length + 2*dst.length := by
  have h := measuredMasked_gateSlots_le c (xs ++ pad.take xs.length) (mask.take (2*xs.length)) dst
    (carry.take (2*xs.length-1)) cin
  have hm : (mask.take (2*xs.length)).length ≤ mask.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
  cases sub <;> simp only [squareRow, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem triangular_gateSlots_le (xs dst pad mask carry : List Wire) (cin : Wire) :
    gateSlots (triangularSquare xs dst pad mask carry cin) ≤ xs.length*(15*mask.length+2*dst.length+1) ∧
    gateSlots (triangularSquareClear xs dst pad mask carry cin) ≤ xs.length*(15*mask.length+2*dst.length+1) := by
  induction xs generalizing dst with
  | nil => simp [triangularSquare, triangularSquareClear]
  | cons c xs ih =>
    cases dst with
    | nil => simp [triangularSquare, triangularSquareClear]
    | cons a ds =>
      cases ds with
      | nil => simp [triangularSquare, triangularSquareClear]
      | cons b dst =>
        have ht := ih dst
        have hf := squareRow_gateSlots_le false c xs pad mask dst carry cin
        have hr := squareRow_gateSlots_le true c xs pad mask dst carry cin
        simp only [triangularSquare, triangularSquareClear, gateSlots_append,
          gateSlots_cons, gateSlots_nil, instructionSlots, List.length_cons]
        by_cases he : xs = []
        · subst xs; simp [triangularSquare, triangularSquareClear]
        · simp only [he, ↓reduceIte]
          constructor <;> nlinarith [ht.1, ht.2]

theorem karatsuba_gateSlots_le (L : KaratsubaSquareLayout) (hw : L.Valid) :
    gateSlots (karatsubaSquare L) ≤ 3000000 ∧ gateSlots (karatsubaSquareClear L) ≤ 3000000 := by
  have hlow := triangular_gateSlots_le L.low L.a L.pad L.mask L.carry L.cin
  have hhigh := triangular_gateSlots_le L.high L.d L.pad L.mask L.carry L.cin
  have hsum := triangular_gateSlots_le L.sum L.c L.pad L.mask L.carry L.cin
  have hprep := addInPlace_gateSlots_le (L.high++L.pad.take 1) L.sum (L.carry.take 128) L.cin
  have hclear := subInPlace_gateSlots_le (L.high++L.pad.take 1) L.sum (L.carry.take 128) L.cin
  have hadda := addInPlace_gateSlots_le (L.a++L.pad) (L.z.drop 128) L.carry L.cin
  have hsuba := subInPlace_gateSlots_le (L.a++L.pad) (L.z.drop 128) L.carry L.cin
  have haddd := addInPlace_gateSlots_le (L.d++L.pad) (L.z.drop 128) L.carry L.cin
  have hsubd := subInPlace_gateSlots_le (L.d++L.pad) (L.z.drop 128) L.carry L.cin
  have haddc := addInPlace_gateSlots_le (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin
  have hsubc := subInPlace_gateSlots_le (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin
  simp only [List.length_append, List.length_take, List.length_drop,
    hw.low_length, hw.high_length, hw.a_length, hw.d_length, hw.c_length,
    hw.z_length, hw.sum_length, hw.pad_length, hw.mask_length] at *
  simp only [karatsubaSquare, karatsubaSquareClear, KaratsubaSquareLayout.squareLow,
    KaratsubaSquareLayout.squareHigh, KaratsubaSquareLayout.squareSum, KaratsubaSquareLayout.clearLow,
    KaratsubaSquareLayout.clearHigh, KaratsubaSquareLayout.clearSquareSum,
    KaratsubaSquareLayout.prepareSum, KaratsubaSquareLayout.clearSum, KaratsubaSquareLayout.copySquares,
    KaratsubaSquareLayout.combine, KaratsubaSquareLayout.uncombine, gateSlots_append, copyRegister_gateSlots,
    List.length_take, List.length_drop, hw.low_length, hw.a_length, hw.d_length, hw.z_length, hw.sum_length]
  constructor <;> omega

theorem squareFold_gateSlots_le (src dst pad carry : List Wire) (cin : Wire) (js : List Nat) :
    gateSlots (squareFoldAdd src dst pad carry cin js) ≤ js.length*(12*(src.length+2*pad.length)+2*dst.length) ∧
    gateSlots (squareFoldClear src dst pad carry cin js) ≤ js.length*(12*(src.length+2*pad.length)+2*dst.length) := by
  induction js with
  | nil => simp [squareFoldAdd, squareFoldClear]
  | cons j js ih =>
    have hl : (shiftedSource src pad j dst.length).length ≤ src.length + 2*pad.length := by
      simp only [shiftedSource, List.length_append, List.length_take, List.length_drop]; omega
    have ha := addInPlace_gateSlots_le (shiftedSource src pad j dst.length) dst (carry.take (dst.length-1)) cin
    have hs := subInPlace_gateSlots_le (shiftedSource src pad j dst.length) dst (carry.take (dst.length-1)) cin
    simp only [squareFoldAdd, squareFoldClear, gateSlots_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    constructor <;> omega

theorem squareReduce_gateSlots_le (L : SquareReduceLayout) (hw : L.Widths) :
    gateSlots (squareReduce L) ≤ 200000 ∧ gateSlots (squareReduceClear L) ≤ 200000 := by
  have hv : L.value.length = 256 := by simp [SquareReduceLayout.value, hw.r]
  have hq : L.quotient.length = 33 := by simp [SquareReduceLayout.quotient, hw.r]
  have he : L.extended.length = 257 := by simp [SquareReduceLayout.extended, hv]
  have hf := squareFold_gateSlots_le L.high L.r L.pad L.carry L.cin squareFoldShifts
  have hg := squareFold_gateSlots_le L.quotient L.extended L.pad L.carry L.cin squareFoldShifts
  have hb := maskedConst_gateSlots_le L.b L.mask L.value (L.carry.take 255) L.cin SquareReduction.c
  have hn := maskedConst_gateSlots_le L.flag L.mask L.value (L.carry.take 255) L.cin SquareReduction.p
  have hc := compareLtConst_gateSlots_le none L.value L.mask (L.carry.take 256) L.cin L.flag SquareReduction.p
  have hlen : squareFoldShifts.length = 7 := rfl
  rw [hlen, hw.high, hw.r, hw.pad] at hf
  rw [hlen, hq, he, hw.pad] at hg
  rw [hw.mask, hv] at hb hn
  rw [hv, hw.mask] at hc
  simp only [squareReduce, squareReduceClear, squareNormalize, squareDenormalize,
    gateSlots_append, copyRegister_gateSlots, hw.low, hv, gateSlots_cons, gateSlots_nil, instructionSlots]
  constructor <;> omega

theorem squareSub_gateSlots_le (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    gateSlots (squareSub L) ≤ 6500000 := by
  have hi := karatsuba_gateSlots_le L.integer (L.integer_valid hw hn)
  have hr := squareReduce_gateSlots_le L.reduction (L.reduction_widths hw)
  have hw' := L.output_widths hw
  have ha := modAddCore_gateSlots_le L.output.toModAddCoreLayout SquareReduction.p
  have hb := negRaw_gateSlots_le L.output SquareReduction.p
  rw [hw'.core.a, hw'.core.constant, hw'.core.low] at ha
  rw [hw'.core.a, hw'.core.constant] at hb
  simp only [squareSub, modSubInPlace, modAddInPlace, gateSlots_append]
  omega

end ECDSAAdd.Baselines
