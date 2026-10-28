import ECDSAAdd.Arithmetic.OffsetBorrowedControlledPort
import ECDSAAdd.Arithmetic.PointRecoveryStage
import ECDSAAdd.Arithmetic.PointInPlaceProgram
import ECDSAAdd.Math.DialogPointFlags

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 一次除法、专用平方、一次乘法；斜率直接存于当前y。 -/
def pointDialogGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  pointDialogConstantAdd L L.point.x (-cx) ++
  pointDialogConstantAdd L L.point.y (-cy) ++
  pointOffsetBorrowedArithmetic L false ++
  pointDialogSquare L ++
  pointDialogConstantAdd L L.point.x (3*cx) ++
  pointOffsetBorrowedArithmetic L true ++
  pointRecoveryStage L cx cy

/-- 标志别名：equalX=hEnable，equalNegY=h；其余三个输入分类仍为o/d/i。 -/
def pointDialogGenericFlag (L : ControlledPointLayout) : Program :=
  pointInPlaceGenericFlag L ++ [.CX L.core.equalNegY L.core.generic]

def pointDialogExceptionEnable (L : ControlledPointLayout) (C : Point) : Program :=
  if !pointEqual (dialogExceptionPoint C) 0 && !pointEqual (dialogExceptionPoint C) C &&
      !pointEqual (dialogExceptionPoint C) (-C) then [.CX L.control L.core.equalX] else []

def pointDialogCorners (L : ControlledPointLayout) (C : Point) : Program :=
  pointInPlaceCorners L C ++
  maskedPointConstant L.core.equalNegY L.point (dialogExceptionPoint C) ++
  maskedPointConstant L.core.equalNegY L.point (-C)

def pointDialogFinite (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode C) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode (-C)) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (dialogExceptionPoint C)) ++
  pointDialogGenericFlag L ++ pointDialogGeneric L cx cy ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode C) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode (C+C)) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (-C)) ++
  pointDialogExceptionEnable L C ++ pointInPlaceDoubleEnable L cy

end ECDSAAdd.Arithmetic
