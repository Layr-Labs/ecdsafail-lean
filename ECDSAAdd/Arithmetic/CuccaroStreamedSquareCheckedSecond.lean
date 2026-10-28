import ECDSAAdd.Arithmetic.CuccaroStreamedSquareCheckedBSuffix
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareCheckedC

set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem checkedSecondHalf_pair (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (base : BasisState)
    (A B O : Nat) (hA : regValue L.core.low base=A)
    (hHigh : regValue L.core.high base=B)
    (hSum : regValue L.core.sum base=B) (hBb : B<2^128)
    (hprod : regValue L.core.product base=0) (hsum : A+B<2^129)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base (B^2) O) L.checkedSecondHalf
      (PairFrame L base 0
        (branchCMiddleValue (A+B) (subTimesProductValue (B^2) O))) := by
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb := L.checkedBranchB_suffix_pair hw hnd base B O hHigh hBb hprod hO hc
  have hc' := L.checkedBranchC_pair_rebased hw hnd base A B
    (subTimesProductValue (B^2) O) hA hSum hsum (Nat.mod_lt _ hp) hc
  rw [L.checkedSecondHalf_eq]
  exact checkedSeq_correct hb hc'

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
