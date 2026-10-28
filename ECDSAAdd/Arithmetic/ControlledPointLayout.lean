import ECDSAAdd.Arithmetic.ControlledPointPorts
import ECDSAAdd.Arithmetic.CompressedPointDialogProgram

namespace ECDSAAdd.Arithmetic
open Secp256k1


/-- 控制只进入三个最终输出标志，候选算术及测量序列不依赖控制值。 -/
def pointSelectors (L : ControlledPointLayout) : Program :=
  [.CCX L.control L.core.generic L.genericSelect,
   .CCX L.control L.core.double L.doubleSelect,
   .X L.core.input.finite,.CCX L.control L.core.input.finite L.infinitySelect,.X L.core.input.finite]

def selectedPointOutput (L : ControlledPointLayout) (C : Point) : Program :=
  pointGenericOutput L.selected++maskedPointConstant L.doubleSelect L.core.output (C+C)++
    maskedPointConstant L.infinitySelect L.core.output C

def controlledPointOutput (L : ControlledPointLayout) (C : Point) : Program :=
  pointSelectors L++selectedPointOutput L C++pointSelectors L

/-- 控制为假的分支也计算并清理候选，只抑制最终输出。 -/
def controlledPointAddOut (L : ControlledPointLayout) (C : Point) : Program :=
  match C with
  | .zero => copyRegister (some L.control) (PointAddLayout.pointWires L.core.input)
      (PointAddLayout.pointWires L.core.output)
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
    pointFlagsCompute L.core cx cy++pointCandidateCompute L.core cx cy++controlledPointOutput L C++
      pointCandidateClear L.core cx cy++pointFlagsClear L.core cx cy

/-- 除法中心原地点加；有限常量执行固定门列，C=O时构造为空。 -/
def controlledPointAdd (L : ControlledPointLayout) (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ => pointCompressedDialogFinite L C cx cy

end ECDSAAdd.Arithmetic
