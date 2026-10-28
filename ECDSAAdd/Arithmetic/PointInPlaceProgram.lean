import ECDSAAdd.Arithmetic.PointKaratsubaLayout
import ECDSAAdd.Math.PointInPlace

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 受控常数模加：掩码源、无控制模加、清源。 -/
def pointInPlaceConstantAdd (L : ControlledPointLayout) (r : List Wire) (k : Fp) : Program :=
  let M := L.inPlaceConstant r
  maskedConstant L.core.generic M.a k.val ++ modAddInPlace M p ++ maskedConstant L.core.generic M.a k.val

/-- 规范取负，两个高位在调用边界均零。 -/
def pointInPlaceNegate (L : ControlledPointLayout) : Program :=
  controlledModSub L.core.generic L.inPlaceNegate p ++
  swapRegisters L.core.generic L.point.x L.inPlaceNegate.low ++
  controlledModAdd L.core.generic L.inPlaceNegate p

/-- 从当前x/y重算斜率；零除数例外用编译期常量清除。 -/
def pointInPlaceClearSlope (L : ControlledPointLayout) (lambdaStar : Fp) : Program :=
  equalConstant L.core.generic L.core.equalX L.inPlaceXZero 0 ++
  [.CX L.core.generic L.core.equalNegY,.CX L.core.equalX L.core.equalNegY] ++
  divideSub (L.inPlaceDivide L.core.equalNegY L.point.x L.point.y) ++
  maskedConstant L.core.equalX L.inPlaceSlope lambdaStar.val ++
  [.CX L.core.generic L.core.equalNegY,.CX L.core.equalX L.core.equalNegY] ++
  equalConstant L.core.generic L.core.equalX L.inPlaceXZero 0

/-- §16.3十二步普通分支；λ在未启用分支始终为零，外部乘积无需外部控制。 -/
def pointInPlaceGeneric (L : ControlledPointLayout) (cx cy lambdaStar : Fp) : Program :=
  pointInPlaceConstantAdd L L.point.x (-cx) ++
  pointInPlaceConstantAdd L L.point.y (-cy) ++
  divideAdd (L.inPlaceDivide L.core.generic L.point.x L.point.y) ++
  montMulSub L.inPlaceMultiply p ++
  squareSub L.inPlaceKaratsuba ++
  pointInPlaceConstantAdd L L.point.x (3*cx) ++
  montMulAdd L.inPlaceMultiply p ++
  pointInPlaceClearSlope L lambdaStar ++
  pointInPlaceNegate L ++
  pointInPlaceConstantAdd L L.point.x cx ++
  pointInPlaceConstantAdd L L.point.y (-cy)

/-- g=b XOR o XOR d XOR i；同一CX序列装载与清理。 -/
def pointInPlaceGenericFlag (L : ControlledPointLayout) : Program :=
  [.CX L.control L.core.generic,.CX L.infinitySelect L.core.generic,
    .CX L.doubleSelect L.core.generic,.CX L.genericSelect L.core.generic]

/-- h=b∧[cy≠−cy]，条件是编译期常量，不添加几何前提。 -/
def pointInPlaceDoubleEnable (L : ControlledPointLayout) (cy : Fp) : Program :=
  if cy≠-cy then [.CX L.control L.core.double] else []

/-- 互斥角落的四次XOR：O→C、C→2C、−C→O。 -/
def pointInPlaceCorners (L : ControlledPointLayout) (C : Point) : Program :=
  maskedPointConstant L.infinitySelect L.point C ++
  maskedPointConstant L.doubleSelect L.point C ++
  maskedPointConstant L.doubleSelect L.point (C+C) ++
  maskedPointConstant L.genericSelect L.point (-C)

/-- 输入分类、普通分支、三个互斥角落写回，再从输出清除分类位。 -/
def pointInPlaceFinite (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++
  equalConstant L.control L.infinitySelect L.inPlacePointZero (pointCode 0) ++
  equalConstant L.core.double L.doubleSelect L.inPlacePointZero (pointCode C) ++
  equalConstant L.control L.genericSelect L.inPlacePointZero (pointCode (-C)) ++
  pointInPlaceGenericFlag L ++
  pointInPlaceGeneric L cx cy (exceptionalSlope C) ++
  pointInPlaceCorners L C ++
  pointInPlaceGenericFlag L ++
  equalConstant L.control L.infinitySelect L.inPlacePointZero (pointCode C) ++
  equalConstant L.core.double L.doubleSelect L.inPlacePointZero (pointCode (C+C)) ++
  equalConstant L.control L.genericSelect L.inPlacePointZero (pointCode 0) ++
  pointInPlaceDoubleEnable L cy

end ECDSAAdd.Arithmetic
