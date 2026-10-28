import ECDSAAdd.Arithmetic.MappedCompressedPointArithmetic
import ECDSAAdd.Arithmetic.CompressedPointSquareCorrect
import ECDSAAdd.Arithmetic.PointDialogProgram
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1 MappedCompressed

/-- 一次除法、专用平方、一次乘法；斜率直接存于当前y。 -/
def pointCompressedDialogGeneric (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  pointDialogConstantAdd L L.point.x (-cx) ++
  pointDialogConstantAdd L L.point.y (-cy) ++
  pointCompressedArithmetic L false ++
  CompressedPointSquare.computableProgram L ++
  pointDialogConstantAdd L L.point.x (3*cx) ++
  pointCompressedArithmetic L true ++
  pointRecoveryStage L cx cy

def pointCompressedDialogFinite (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode C) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode (-C)) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (dialogExceptionPoint C)) ++
  pointDialogGenericFlag L ++ pointCompressedDialogGeneric L cx cy ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode C) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode (C+C)) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (-C)) ++
  pointDialogExceptionEnable L C ++ pointInPlaceDoubleEnable L cy

/-- Candidate full in-place point addition; infinity constant emits no gates. -/
def pointCompressedAdd (L : ControlledPointLayout) (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _hc =>
      pointCompressedDialogFinite L C cx cy

end ECDSAAdd.Arithmetic
