/- PR #80 的值走点加路径；与 Skywalk 共享布局、语义及基础算术。 -/
import ECDSAAdd.Arithmetic.PointDialogProgram
import ECDSAAdd.Arithmetic.ValueWalkPointSteps
import ECDSAAdd.Math.DialogPointFlags

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- 一次除法、专用平方、一次乘法；斜率直接存于当前y。 -/
def valueWalkPointDialogGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  valueWalkPointDialogConstantAdd L L.point.x (-cx) ++
  valueWalkPointDialogConstantAdd L L.point.y (-cy) ++
  dialogDivide L.dialogPort p ++
  valueWalkPointDialogSquare L ++
  valueWalkPointDialogConstantAdd L L.point.x (3*cx) ++
  dialogMultiply L.dialogPort p ++
  valueWalkPointDialogNegate L ++
  valueWalkPointDialogConstantAdd L L.point.x cx ++
  valueWalkPointDialogConstantAdd L L.point.y (-cy)

/-- 完整有限加数程序，复用共同的输入分类和角落处理。 -/
def valueWalkPointDialogFinite (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode C) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode (-C)) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (dialogExceptionPoint C)) ++
  pointDialogGenericFlag L ++ valueWalkPointDialogGeneric L cx cy ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode C) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode (C+C)) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (-C)) ++
  pointDialogExceptionEnable L C ++ pointInPlaceDoubleEnable L cy

end ECDSAAdd.Arithmetic
