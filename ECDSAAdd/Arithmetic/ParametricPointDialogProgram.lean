import ECDSAAdd.Arithmetic.PointArithmeticBackend
import ECDSAAdd.Arithmetic.CompressedPointDialogProgram
namespace ECDSAAdd.Arithmetic.ParametricPointDialog
open ControlledPointLayout Secp256k1
/-- 一次除法、专用平方、一次乘法；斜率直接存于当前y。 -/
def generic (backend : PointArithmeticBackend) (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  pointDialogConstantAdd L L.point.x (-cx) ++
  pointDialogConstantAdd L L.point.y (-cy) ++
  backend.program L false ++
  CompressedPointSquare.computableProgram L ++
  pointDialogConstantAdd L L.point.x (3*cx) ++
  backend.program L true ++
  pointRecoveryStage L cx cy

def finite (backend : PointArithmeticBackend) (L : ControlledPointLayout) (C : Point) (cx cy : Fp) : Program :=
  pointInPlaceDoubleEnable L cy ++ pointDialogExceptionEnable L C ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode C) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode (-C)) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (dialogExceptionPoint C)) ++
  pointDialogGenericFlag L ++ generic backend L cx cy ++ pointDialogCorners L C ++
  pointDialogGenericFlag L ++
  equalConstant L.control L.infinitySelect L.dialogPointZero (pointCode C) ++
  equalConstant L.core.double L.doubleSelect L.dialogPointZero (pointCode (C+C)) ++
  equalConstant L.control L.genericSelect L.dialogPointZero (pointCode 0) ++
  equalConstant L.core.equalX L.core.equalNegY L.dialogPointZero (pointCode (-C)) ++
  pointDialogExceptionEnable L C ++ pointInPlaceDoubleEnable L cy

/-- Candidate full in-place point addition; infinity constant emits no gates. -/
def program (backend : PointArithmeticBackend) (L : ControlledPointLayout) (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _hc =>
      finite backend L C cx cy


/-- Instantiating the interface preserves the existing emitted gate list. -/
theorem skywalk_program (L : ControlledPointLayout) (C : Point) :
    program PointArithmeticBackend.skywalk L C=pointCompressedAdd L C := by
  cases C <;> rfl
end ECDSAAdd.Arithmetic.ParametricPointDialog
