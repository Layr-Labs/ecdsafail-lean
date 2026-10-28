import ECDSAAdd.Arithmetic.PointAddLayout
import ECDSAAdd.Arithmetic.SubtractPorts
import ECDSAAdd.Arithmetic.MultiplyPorts
import ECDSAAdd.Arithmetic.InversePorts
import ECDSAAdd.Arithmetic.SafeDivisor
import ECDSAAdd.Arithmetic.FieldAddSub
import ECDSAAdd.Arithmetic.FieldMultiply
import ECDSAAdd.Arithmetic.InverseResources

namespace ECDSAAdd.Arithmetic

namespace PointAddLayout

def poolWire (L : PointAddLayout) : Nat → Wire := fun i => L.pool.getD i 0

def extendedX (L : PointAddLayout) : List Wire := L.input.x++[L.inputXHigh]
def extendedY (L : PointAddLayout) : List Wire := L.input.y++[L.inputYHigh]

end PointAddLayout

/-- 常量工作字装载后立即卸载；输入输出直接连接模减法接口。 -/
def pointSubConstant (L : PointAddLayout) (x out : List Wire) (k : Nat) : Program :=
  xorConstant L.constant k++fieldSub (poolSub L.poolWire x L.constant out)++
    xorConstant L.constant k

/-- 平方使用独立乘数副本，避免重复控制线；复制前后不计 Toffoli。 -/
def pointSquare (L : PointAddLayout) : Program :=
  copyRegister none L.slope L.constant++
    fieldMul (poolMul L.poolWire L.slope (L.constant.take 256) L.square)++
    copyRegister none L.slope L.constant

/-- 普通候选在每一条分支上计算。分支标志预先确定，安全除数保证求逆定义域。 -/
def pointCandidateCompute (L : PointAddLayout) (cx cy : Fp) : Program :=
  pointSubConstant L L.extendedX L.dx cx.val++
  pointSubConstant L L.extendedY L.dy cy.val++
  safeDivisor L.generic (L.dx.take 256) L.divisor.head! L.divisor.tail++
  fieldInverse (poolInverse L.poolWire L.divisor L.inverse)++
  fieldMul (poolMul L.poolWire L.dy L.inverse L.slope)++
  pointSquare L++
  fieldSub (poolSub L.poolWire L.square L.extendedX L.offset)++
  pointSubConstant L L.offset L.candidateX cx.val++
  fieldSub (poolSub L.poolWire L.extendedX L.candidateX L.delta)++
  fieldMul (poolMul L.poolWire L.delta (L.slope.take 256) L.product)++
  fieldSub (poolSub L.poolWire L.product L.extendedY L.candidateY)

/-- 按依赖的逆序重新执行前向 XOR 模块；没有反转测量程序或依赖测量结果选路。 -/
def pointCandidateClear (L : PointAddLayout) (cx cy : Fp) : Program :=
  fieldSub (poolSub L.poolWire L.product L.extendedY L.candidateY)++
  fieldMul (poolMul L.poolWire L.delta (L.slope.take 256) L.product)++
  fieldSub (poolSub L.poolWire L.extendedX L.candidateX L.delta)++
  pointSubConstant L L.offset L.candidateX cx.val++
  fieldSub (poolSub L.poolWire L.square L.extendedX L.offset)++
  pointSquare L++
  fieldMul (poolMul L.poolWire L.dy L.inverse L.slope)++
  fieldInverse (poolInverse L.poolWire L.divisor L.inverse)++
  safeDivisor L.generic (L.dx.take 256) L.divisor.head! L.divisor.tail++
  pointSubConstant L L.extendedY L.dy cy.val++
  pointSubConstant L L.extendedX L.dx cx.val

end ECDSAAdd.Arithmetic
