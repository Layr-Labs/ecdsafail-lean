import ECDSAAdd.Arithmetic.CuccaroStreamedSquareCheckedFirst
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareCheckedSecond

set_option maxHeartbeats 8000000
set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

private theorem addRotateProductValue_lt (P O : Nat) :
    addRotateProductValue P O false<SquareReduction.p := by
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  unfold addRotateProductValue addRotate128Value
  simp only [Bool.false_eq_true,if_false]
  unfold addCMinusOneValue addModValue subModValue
  exact Nat.mod_lt _ hp

attribute [local irreducible] branchAValue addRotateProductValue
  subTimesProductValue branchCMiddleValue

/-- The three independently verified streamed branches compose without
expanding their gate streams.  Keeping the value expression abstract here is
intentional: the following arithmetic lemma identifies it with subtraction of
the full 256-bit square modulo `p`. -/
theorem program_pair_raw (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B O : Nat)
    (hA : regValue L.core.low base=A) (hAb : A<2^128)
    (hB : regValue L.core.high base=B) (hBb : B<2^128)
    (hsumCarry : base L.core.sumCarry=false)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p)
    (hsum : A+B<2^129) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.checkedProgram
      (PairFrame L base 0
        (branchCMiddleValue (A+B)
          (subTimesProductValue (B^2)
            (addRotateProductValue (B^2) (branchAValue A O) false)))) := by
  have first := L.checkedFirstHalf_pair hw hnd base A B O hA hAb hB hprod hO hc
  have hsumValue : regValue L.core.sum base=B := by
    rw [CuccaroStreamedSquareLayout.sum,regValue_append,hB]
    change B+2^L.core.high.length*(if base L.core.sumCarry then 1 else 0)=B
    simp [hsumCarry]
  have second := L.checkedSecondHalf_pair hw hnd base A B
    (addRotateProductValue (B^2) (branchAValue A O) false) hA hB hsumValue hBb
    hprod hsum (addRotateProductValue_lt (B^2) (branchAValue A O)) hc
  rw [L.checkedProgram_eq]
  exact checkedSeq_correct first second

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
