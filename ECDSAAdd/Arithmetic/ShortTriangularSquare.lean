/- PR #81 的短源三角平方变体；与原三角平方共享基础加法器及状态断言。 -/
import ECDSAAdd.Arithmetic.MeasuredShortAdder
import ECDSAAdd.Math.Square

namespace ECDSAAdd.Arithmetic.ShortTriangular

/-- Exact cross-term row: zero extension is implicit in the clean full-width mask.
The padding argument is retained for layout API compatibility but is untouched. -/
def squareRow (sub : Bool) (c : Wire) (xs _pad mask dst carry : List Wire) (cin : Wire) : Program :=
  let tmp := mask.take (2*xs.length)
  let cy := carry.take (2*xs.length-1)
  if sub then measuredShortSubInPlace c xs tmp dst cy cin
  else measuredShortAddInPlace c xs tmp dst cy cin

/-- X²的对称三角门列；高位平方先完成，然后累加低位的交叉项。 -/
def triangularSquare : List Wire → List Wire → List Wire → List Wire → List Wire → Wire → Program
  | [], _, _, _, _, _ => []
  | c::xs, a::_b::dst, pad, mask, carry, cin =>
    triangularSquare xs dst pad mask carry cin ++
      (if xs=[] then [] else squareRow false c xs pad mask dst carry cin) ++ [.CX c a]
  | _, _, _, _, _, _ => []

/-- 使用新的减法测量记录清理已知平方，绝不倒放测量指令。 -/
def triangularSquareClear : List Wire → List Wire → List Wire → List Wire → List Wire → Wire → Program
  | [], _, _, _, _, _ => []
  | c::xs, a::_b::dst, pad, mask, carry, cin =>
    [.CX c a] ++ (if xs=[] then [] else squareRow true c xs pad mask dst carry cin) ++
      triangularSquareClear xs dst pad mask carry cin
  | _, _, _, _, _, _ => []

end ECDSAAdd.Arithmetic.ShortTriangular
