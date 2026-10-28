import ECDSAAdd.Arithmetic.CuccaroStreamedSquare

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareLayout

def overhang0 (L : CuccaroStreamedSquareLayout) : Wire := L.product.getD 256 0
def overhang1 (L : CuccaroStreamedSquareLayout) : Wire := L.product.getD 257 0
def threshold128 (L : CuccaroStreamedSquareLayout) : Wire := L.work.getD 128 0
def threshold129 (L : CuccaroStreamedSquareLayout) : Wire := L.work.getD 129 0

def overhangNonzero (L : CuccaroStreamedSquareLayout) : Program :=
  [.CX L.overhang0 L.normFlag,.CX L.overhang1 L.normFlag,
    .CCX L.overhang0 L.overhang1 L.normFlag]

/-- Exact subtraction of the two-bit 258-bit-square overhang.

The first widened subtraction retains its borrow in `outHigh`.  After adding
`p` back on that branch, a second widened subtraction compares the canonical
result with `p-E*2^128`.  The threshold is `p` with bits 128/129 toggled by
the two overhang controls.  This recovers and clears the retained borrow while
returning every work bit to zero. -/
def overhangSub (L : CuccaroStreamedSquareLayout) : Program :=
  let src257 := L.work++[L.workHigh]
  let dst257 := L.out++[L.outHigh]
  let cmp257 := L.out++[L.productHigh]
  maskedConstant L.overhang0 L.work (2^128)++
  maskedConstant L.overhang1 L.work (2^129)++
  cuccaroSub src257 dst257 L.cin++
  maskedConstant L.overhang1 L.work (2^129)++
  maskedConstant L.overhang0 L.work (2^128)++
  maskedConstant L.outHigh L.work SquareReduction.p++
  cuccaroAdd L.work L.out L.cin++
  maskedConstant L.outHigh L.work SquareReduction.p++
  xorConstant L.work SquareReduction.p++
  [.CX L.overhang0 L.threshold128,.CX L.overhang1 L.threshold129]++
  cuccaroSub src257 cmp257 L.cin++
  L.overhangNonzero++
  [.X L.productHigh,.CCX L.normFlag L.productHigh L.outHigh,.X L.productHigh]++
  L.overhangNonzero.reverse++
  (cuccaroSub src257 cmp257 L.cin).reverse++
  [.CX L.overhang1 L.threshold129,.CX L.overhang0 L.threshold128]++
  xorConstant L.work SquareReduction.p

theorem overhangSub_counts (L : CuccaroStreamedSquareLayout) (hw : L.Widths) :
    toffoliCount L.overhangSub=2049 ∧ measurementCount L.overhangSub=0 := by
  have srcLen : (L.work++[L.workHigh]).length=257 := by simp [hw.work]
  have dstLen : (L.out++[L.outHigh]).length=257 := by simp [hw.out]
  have cmpLen : (L.out++[L.productHigh]).length=257 := by simp [hw.out]
  have sub1 := cuccaroSub_counts (L.work++[L.workHigh])
    (L.out++[L.outHigh]) L.cin (srcLen.trans dstLen.symm)
  have sub2 := cuccaroSub_counts (L.work++[L.workHigh])
    (L.out++[L.productHigh]) L.cin (srcLen.trans cmpLen.symm)
  have add := cuccaroAdd_counts L.work L.out L.cin (hw.work.trans hw.out.symm)
  simp [overhangSub,overhangNonzero,toffoliCount_append,measurementCount_append,
    toffoliCount_reverse,measurementCount_reverse,sub1.1,sub1.2,sub2.1,sub2.2,
    add.1,add.2,(maskedConstant_counts _ _ _).1,
    (maskedConstant_counts _ _ _).2,(xorConstant_counts _ _).1,
    (xorConstant_counts _ _).2,toffoliCount,measurementCount,hw.out]

end CuccaroStreamedSquareLayout
end ECDSAAdd.Arithmetic
