import ECDSAAdd.Arithmetic.CuccaroStreamedSquareProof

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

theorem branchB_suffix_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (B O : Nat)
    (hB : regValue L.core.high base=B) (hBb : B<2^128)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base (B^2) O)
      (L.subTimesC (L.core.product.take 256)++L.core.square128Clear L.core.high)
      (PairFrame L base 0 (subTimesProductValue (B^2) O)) := by
  have highLen := L.core.high_length hw.core
  have highCount (q : Wire) : L.core.high.count q≤L.core.y.count q := by
    have h1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have h2 := (List.drop_sublist 128 L.core.y).count_le q
    simpa [CuccaroStreamedSquareLayout.high] using h1.trans h2
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let O2 := subTimesProductValue (B^2) O
  have timesT := L.subTimesC_pair hw hnd base (B^2) O hO hc
  have clrT := L.square128Clear_pair hw hnd L.core.high highLen highCount base B O2
    hB hBb hprod (PairClean.corePad L base hc) hc.work hc.cin
  intro s records hs
  let s1 := run (L.subTimesC (L.core.product.take 256)) [] s
  let s2 := run (L.core.square128Clear L.core.high) records s1
  have e1 := timesT s [] hs
  have e2 := clrT s1 records e1.2
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have timesm := L.subTimesC_counts hw (L.core.product.take 256) p256
  have exec : run
      (L.subTimesC (L.core.product.take 256)++L.core.square128Clear L.core.high)
      records s=s2 := by
    simp [s1,s2,run_append,timesm.2]
  rw [exec]
  exact ⟨e2.1.trans e1.1,e2.2⟩

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
