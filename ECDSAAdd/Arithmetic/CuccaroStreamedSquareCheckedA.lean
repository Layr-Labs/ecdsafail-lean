import ECDSAAdd.Arithmetic.CuccaroStreamedSquareOpaque

set_option maxRecDepth 5000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem checkedBranchA_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A O : Nat)
    (hA : regValue L.core.low base=A) (hAb : A<2^128)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O) L.checkedBranchA
      (PairFrame L base 0 (branchAValue A O)) := by
  rw [L.checkedBranchA_eq]
  exact L.branchA_pair hw hnd base A O hA hAb hprod hO hc

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
