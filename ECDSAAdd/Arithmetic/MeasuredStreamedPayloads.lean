import ECDSAAdd.Arithmetic.MeasuredStreamedViews
import ECDSAAdd.Math.StreamedSquareValues

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measuredSignedSum_append (base : BasisState) (a b : List MeasuredSquareFold) :
    measuredSignedSum base (a++b)=measuredSignedSum base a+measuredSignedSum base b := by
  induction a with
  | nil => simp [measuredSignedSum]
  | cons f fs ih => simp [measuredSignedSum,ih,add_assoc]

theorem measured_naf_sum (base : BasisState) (src : List Wire) (negative : Bool) :
    measuredSignedSum base (nafMinusOneItems negative src)=
      if negative then -((SquareReduction.c : ZMod SquareReduction.p)-1)*(regValue src base : ZMod SquareReduction.p)
      else ((SquareReduction.c : ZMod SquareReduction.p)-1)*(regValue src base : ZMod SquareReduction.p) := by
  cases negative <;>
    simp [nafMinusOneItems,measuredSignedSum,measuredSignedPayload,measuredFoldPayload,Nat.cast_mul] <;>
    norm_num [SquareReduction.c] <;> ring

def measuredPositiveRotateItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  [{negative:=false,canonical:=true,src:=L.rotated128}]++
    nafMinusOneItems false (L.core.product.drop 128)

theorem measured_positive_rotate_sum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (P : Nat) (hP : regValue L.core.product base=P) (hb : P<2^256) :
    measuredSignedSum base L.measuredPositiveRotateItems=(P : ZMod SquareReduction.p)*2^128 := by
  have value := addRotateProductValue_cast P 0 hb
  simp only [addRotateProductValue,addRotate128Value,Bool.false_eq_true,if_false,addCMinusOneValue_cast,
    addModValue_cast,Nat.cast_zero,zero_add] at value
  simp only [measuredPositiveRotateItems,measuredSignedSum_append,measuredSignedSum,
    measuredSignedPayload,measuredFoldPayload,Bool.false_eq_true,if_false,Nat.pow_zero,Nat.mul_one,add_zero,
    measured_naf_sum,L.rotated128_value hw base P hP,L.product_drop_value hw base P hP 128 (by omega)]
  simpa only [add_zero] using value

theorem measured_shifted_sum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (P : Nat) (hP : regValue L.core.product base=P) (hb : P<2^256)
    (negative : Bool) (j : Nat) (hj : j≤256) :
    measuredSignedSum base (shiftedProductItems negative (L.core.product.take 256) j)=
      if negative then -(P : ZMod SquareReduction.p)*2^j else (P : ZMod SquareReduction.p)*2^j := by
  have source := L.product_take_value hw base P hP 256 (by omega)
  rw [Nat.mod_eq_of_lt hb] at source
  by_cases zero : j=0
  · subst j
    cases negative <;> simp [shiftedProductItems,measuredSignedSum,measuredSignedPayload,measuredFoldPayload,source]
  · have target := shiftedFull_cast P j hj hb
    have rot := L.rotateFull_value hw base P hP j hj
    have high := L.productTakeDrop_value hw base P hP j hj
    cases h : negative
    · simp only [shiftedProductItems,zero,if_false,measuredSignedSum_append,measuredSignedSum,
        measuredSignedPayload,measuredFoldPayload,Bool.false_eq_true,if_false,Nat.pow_zero,Nat.mul_one,
        add_zero,measured_naf_sum,rot,high]
      simpa only [rotatedFullValue,highFullValue] using target
    · simp only [shiftedProductItems,zero,if_false,measuredSignedSum_append,measuredSignedSum,
        measuredSignedPayload,measuredFoldPayload,if_true,Nat.pow_zero,Nat.mul_one,
        add_zero,measured_naf_sum,rot,high]
      simp only [rotatedFullValue,highFullValue] at target
      linear_combination -target

theorem measuredA_sum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (P : Nat) (hP : regValue L.core.product base=P) (hb : P<2^256) :
    measuredSignedSum base L.measuredAItems=
      (P : ZMod SquareReduction.p)*2^128-P := by
  have rot := L.measured_positive_rotate_sum hw base P hP hb
  have source := L.product_take_value hw base P hP 256 (by omega)
  rw [Nat.mod_eq_of_lt hb] at source
  have split : L.measuredAItems=
      [{negative:=true,canonical:=true,src:=L.core.product.take 256}]++L.measuredPositiveRotateItems := rfl
  rw [split,measuredSignedSum_append,rot]
  simp [measuredSignedSum,measuredSignedPayload,measuredFoldPayload,source]
  ring

theorem measuredB_sum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (P : Nat) (hP : regValue L.core.product base=P) (hb : P<2^256) :
    measuredSignedSum base L.measuredBItems=
      (P : ZMod SquareReduction.p)*2^128-SquareReduction.c*P := by
  have rot := L.measured_positive_rotate_sum hw base P hP hb
  have sh0 := L.measured_shifted_sum hw base P hP hb true 0 (by omega)
  have sh4 := L.measured_shifted_sum hw base P hP hb true 4 (by omega)
  have sh6 := L.measured_shifted_sum hw base P hP hb false 6 (by omega)
  have sh10 := L.measured_shifted_sum hw base P hP hb true 10 (by omega)
  have sh32 := L.measured_shifted_sum hw base P hP hb true 32 (by omega)
  have split : L.measuredBItems=L.measuredPositiveRotateItems++
      shiftedProductItems true (L.core.product.take 256) 0++
      shiftedProductItems true (L.core.product.take 256) 4++
      shiftedProductItems false (L.core.product.take 256) 6++
      shiftedProductItems true (L.core.product.take 256) 10++
      shiftedProductItems true (L.core.product.take 256) 32 := rfl
  rw [split,measuredSignedSum_append,measuredSignedSum_append,measuredSignedSum_append,
    measuredSignedSum_append,measuredSignedSum_append,rot,sh0,sh4,sh6,sh10,sh32]
  norm_num [SquareReduction.c]
  ring

theorem measuredC_sum (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (base : BasisState) (P : Nat) (hP : regValue L.core.product base=P) :
    measuredSignedSum base L.measuredCItems=-(P : ZMod SquareReduction.p)*2^128 := by
  have target := subRotateProductValue_cast P 0
  simp only [subRotateProductValue,subRotate128Value,if_true,subModValue_cast,
    subCMinusOneValue_cast,Nat.cast_zero,zero_sub] at target
  simp only [measuredCItems,measuredSignedSum_append,measuredSignedSum,
    measuredSignedPayload,measuredFoldPayload,if_true,Nat.pow_zero,Nat.mul_one,add_zero,
    measured_naf_sum,L.rotated128_value hw base P hP,L.product_drop_value hw base P hP 128 (by omega),
    L.product_drop_value hw base P hP 256 (by omega),Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at target
  linear_combination target

theorem measured_concrete_orientations (L : CuccaroStreamedSquareWideLayout) :
    measuredFinalOrientation false L.measuredAItems=false ∧
    measuredFinalOrientation false L.measuredBItems=true ∧
    measuredFinalOrientation true L.measuredCItems=true := by
  simp [measuredFinalOrientation,measuredAItems,measuredBItems,measuredCItems,
    shiftedProductItems,nafMinusOneItems]

/-- Exact controlled Karatsuba identity for the three leaf contributions.
The radix congruence is secp256k1's p = 2^256 - c, not an approximation. -/
theorem measured_controlled_square_identity (enabled : Bool) (A B : Nat) :
    (((if enabled then A else 0)^2 : Nat) : ZMod SquareReduction.p)*2^128-
      (((if enabled then A else 0)^2 : Nat) : ZMod SquareReduction.p)+
      ((((if enabled then B else 0)^2 : Nat) : ZMod SquareReduction.p)*2^128-
        SquareReduction.c*(((if enabled then B else 0)^2 : Nat) : ZMod SquareReduction.p))-
      (((if enabled then A+B else 0)^2 : Nat) : ZMod SquareReduction.p)*2^128=
        -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) := by
  cases enabled
  · simp
  · simp only [if_true,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    have radix : ((2 : ZMod SquareReduction.p)^128)^2=SquareReduction.c := by
      rw [←pow_mul]
      exact radix_cast
    rw [←radix]
    ring

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
