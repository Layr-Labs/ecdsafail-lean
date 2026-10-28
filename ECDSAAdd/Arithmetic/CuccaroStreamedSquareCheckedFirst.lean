import ECDSAAdd.Arithmetic.CuccaroStreamedSquareCheckedA
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareCheckedBPrefix

set_option maxRecDepth 20000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

private theorem branchAValue_lt (A O : Nat) :
    branchAValue A O<SquareReduction.p := by
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  unfold branchAValue addRotateProductValue addRotate128Value
  simp only [Bool.false_eq_true,if_false]
  unfold addCMinusOneValue addModValue subModValue
  exact Nat.mod_lt _ hp

attribute [local irreducible] branchAValue addRotateProductValue

theorem checkedFirstHalf_pair (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (base : BasisState)
    (A B O : Nat) (hA : regValue L.core.low base=A) (hAb : A<2^128)
    (hB : regValue L.core.high base=B)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.checkedFirstHalf
      (PairFrame L base (B^2)
        (addRotateProductValue (B^2) (branchAValue A O) false)) := by
  have ha := L.checkedBranchA_pair hw hnd base A O hA hAb hprod hO hc
  have hb := L.checkedBranchB_prefix_pair hw hnd base B (branchAValue A O) hB
    (branchAValue_lt A O) hc
  rw [L.checkedFirstHalf_eq]
  exact checkedSeq_correct ha hb

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
