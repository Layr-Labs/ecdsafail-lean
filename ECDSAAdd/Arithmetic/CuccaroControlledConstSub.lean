import ECDSAAdd.Arithmetic.CuccaroOverhang

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareLayout

/-- Exact controlled subtraction of a fixed canonical constant modulo the
secp256k1 prime, using no source mask or carry bank.

The first widened subtraction retains its borrow in `outHigh`; the conditional
add-back makes the low word canonical.  Comparing the result with `p-A`
recovers that borrow when the external control is set, so one CCX clears it. -/
def controlledConstSub (L : CuccaroStreamedSquareLayout)
    (control : Wire) (A : Nat) : Program :=
  let src257 := L.work++[L.workHigh]
  let dst257 := L.out++[L.outHigh]
  let cmp257 := L.out++[L.productHigh]
  maskedConstant control L.work A++
  cuccaroSub src257 dst257 L.cin++
  maskedConstant control L.work A++
  maskedConstant L.outHigh L.work SquareReduction.p++
  cuccaroAdd L.work L.out L.cin++
  maskedConstant L.outHigh L.work SquareReduction.p++
  xorConstant L.work (SquareReduction.p-A)++
  cuccaroSub src257 cmp257 L.cin++
  [.X L.productHigh,.CCX control L.productHigh L.outHigh,.X L.productHigh]++
  (cuccaroSub src257 cmp257 L.cin).reverse++
  xorConstant L.work (SquareReduction.p-A)

theorem controlledConstSub_counts (L : CuccaroStreamedSquareLayout)
    (hw : L.Widths) (control : Wire) (A : Nat) :
    toffoliCount (L.controlledConstSub control A)=2047 ∧
      measurementCount (L.controlledConstSub control A)=0 := by
  have srcLen : (L.work++[L.workHigh]).length=257 := by simp [hw.work]
  have dstLen : (L.out++[L.outHigh]).length=257 := by simp [hw.out]
  have cmpLen : (L.out++[L.productHigh]).length=257 := by simp [hw.out]
  have sub1 := cuccaroSub_counts (L.work++[L.workHigh])
    (L.out++[L.outHigh]) L.cin (srcLen.trans dstLen.symm)
  have sub2 := cuccaroSub_counts (L.work++[L.workHigh])
    (L.out++[L.productHigh]) L.cin (srcLen.trans cmpLen.symm)
  have add := cuccaroAdd_counts L.work L.out L.cin (hw.work.trans hw.out.symm)
  simp [controlledConstSub,toffoliCount_append,measurementCount_append,
    toffoliCount_reverse,measurementCount_reverse,sub1.1,sub1.2,sub2.1,sub2.2,
    add.1,add.2,(maskedConstant_counts _ _ _).1,
    (maskedConstant_counts _ _ _).2,(xorConstant_counts _ _).1,
    (xorConstant_counts _ _).2,toffoliCount,measurementCount,hw.out]

def shortPowerFold (L : CuccaroStreamedSquareLayout) :
    List Wire → Nat → Bool → Program
  | [], _, _ => []
  | c::cs, shift, subtract =>
      L.controlledConstSub c
        (if subtract then 2^shift else SquareReduction.p-2^shift)++
      L.shortPowerFold cs (shift+1) subtract

theorem shortPowerFold_counts (L : CuccaroStreamedSquareLayout)
    (hw : L.Widths) (src : List Wire) (shift : Nat) (subtract : Bool) :
    toffoliCount (L.shortPowerFold src shift subtract)=2047*src.length ∧
      measurementCount (L.shortPowerFold src shift subtract)=0 := by
  induction src generalizing shift with
  | nil => simp [shortPowerFold,toffoliCount,measurementCount]
  | cons c cs ih =>
      have h := L.controlledConstSub_counts hw c
        (if subtract then 2^shift else SquareReduction.p-2^shift)
      simp [shortPowerFold,toffoliCount_append,measurementCount_append,
        h.1,h.2,ih]
      omega

end CuccaroStreamedSquareLayout
end ECDSAAdd.Arithmetic
