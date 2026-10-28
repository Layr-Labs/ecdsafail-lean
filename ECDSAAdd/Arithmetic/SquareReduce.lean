import ECDSAAdd.Arithmetic.SquareFold
import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Math.SquareReduction

namespace ECDSAAdd.Arithmetic

/-- 三次折叠的实际寄存器。q 留在 r 的高33位，b 独立于 q。 -/
structure SquareReduceLayout where
  low : List Wire
  high : List Wire
  r : List Wire
  pad : List Wire
  mask : List Wire
  carry : List Wire
  cin : Wire
  b : Wire
  flag : Wire

namespace SquareReduceLayout

def value (L : SquareReduceLayout) := L.r.take 256
def quotient (L : SquareReduceLayout) := L.r.drop 256
def extended (L : SquareReduceLayout) := L.value ++ [L.b]
def wires (L : SquareReduceLayout) :=
  L.low ++ L.high ++ L.r ++ L.pad ++ L.mask ++ L.carry ++ [L.cin,L.b,L.flag]

structure Widths (L : SquareReduceLayout) : Prop where
  low : L.low.length=256
  high : L.high.length=256
  r : L.r.length=289
  pad : L.pad.length=256
  mask : L.mask.length=256
  carry : L.carry.length=383

end SquareReduceLayout

def squareFoldShifts : List Nat := [0,4,6,7,8,9,32]

/-- W 减 p 并留下 f=[W≥p]；f 在输出更新后才清理。 -/
def squareNormalize (L : SquareReduceLayout) : Program :=
  compareLtConst none L.value L.mask (L.carry.take 256) L.cin L.flag SquareReduction.p ++
  [.X L.flag] ++
  maskedSubConst L.flag L.mask L.value (L.carry.take 255) L.cin SquareReduction.p

def squareDenormalize (L : SquareReduceLayout) : Program :=
  maskedAddConst L.flag L.mask L.value (L.carry.take 255) L.cin SquareReduction.p ++
  [.X L.flag] ++
  compareLtConst none L.value L.mask (L.carry.take 256) L.cin L.flag SquareReduction.p

/-- R=l+c*h；第二折叠的257位目标必须用独立 b，不能覆盖 q 的最低位。 -/
def squareReduce (L : SquareReduceLayout) : Program :=
  copyRegister none L.low L.value ++
  squareFoldAdd L.high L.r L.pad L.carry L.cin squareFoldShifts ++
  squareFoldAdd L.quotient L.extended L.pad L.carry L.cin squareFoldShifts ++
  maskedAddConst L.b L.mask L.value (L.carry.take 255) L.cin SquareReduction.c ++
  squareNormalize L

/-- 独立前向减法门列恢复，保留的 q/b/f 依次消去。 -/
def squareReduceClear (L : SquareReduceLayout) : Program :=
  squareDenormalize L ++
  maskedSubConst L.b L.mask L.value (L.carry.take 255) L.cin SquareReduction.c ++
  squareFoldClear L.quotient L.extended L.pad L.carry L.cin squareFoldShifts ++
  squareFoldClear L.high L.r L.pad L.carry L.cin squareFoldShifts ++
  copyRegister none L.low L.value

end ECDSAAdd.Arithmetic
