import ECDSAAdd.Arithmetic.CuccaroStreamedSquareOpaque

set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem checkedBranchB_suffix_pair (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (base : BasisState) (B O : Nat)
    (hB : regValue L.core.high base=B) (hBb : B<2^128)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base (B^2) O) L.checkedBranchBSuffix
      (PairFrame L base 0 (subTimesProductValue (B^2) O)) := by
  rw [L.checkedBranchBSuffix_eq]
  exact L.branchB_suffix_pair hw hnd base B O hB hBb hprod hO hc

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
