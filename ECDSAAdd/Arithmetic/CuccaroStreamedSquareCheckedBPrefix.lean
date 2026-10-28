import ECDSAAdd.Arithmetic.CuccaroStreamedSquareOpaque

set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem checkedBranchB_prefix_pair (L : CuccaroStreamedSquareWideLayout)
    (hw : L.Widths) (hnd : L.wires.Nodup) (base : BasisState) (B O : Nat)
    (hB : regValue L.core.high base=B)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.checkedBranchBPrefix
      (PairFrame L base (B^2) (addRotateProductValue (B^2) O false)) := by
  rw [L.checkedBranchBPrefix_eq]
  exact L.branchB_prefix_pair hw hnd base B O hB hO hc

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
