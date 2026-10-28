import ECDSAAdd.Arithmetic.MeasuredMaskedAdder
import ECDSAAdd.Math.Square

namespace ECDSAAdd.Arithmetic

/-- 平方的交叉项行；padding、mask和carry均借用其所需前缀。 -/
def squareRow (sub : Bool) (c : Wire) (xs pad mask dst carry : List Wire) (cin : Wire) : Program :=
  let src := xs ++ pad.take xs.length
  let tmp := mask.take (2*xs.length)
  let cy := carry.take (2*xs.length-1)
  if sub then measuredMaskedSubInPlace c src tmp dst cy cin
  else measuredMaskedAddInPlace c src tmp dst cy cin

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

end ECDSAAdd.Arithmetic
