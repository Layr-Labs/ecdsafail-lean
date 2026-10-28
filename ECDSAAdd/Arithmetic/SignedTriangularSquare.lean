import ECDSAAdd.Arithmetic.InPlaceAdder
import ECDSAAdd.Arithmetic.ModInPlaceCopy

namespace ECDSAAdd.Arithmetic

/-- Clifford fanout from one control into a list of targets. -/
def cxFrom (c : Wire) (ys : List Wire) : Program := ys.map (Instr.CX c)

/-- Complement every target exactly when `c` is false, preserving `c`.
The per-target form keeps its all-state semantics easy to expose to Lean. -/
def xorWhenFalse (c : Wire) : List Wire → Program
  | [] => []
  | y::ys => [.X y, .CX c y] ++ xorWhenFalse c ys

/-- One exact signed triangular row.

The ordinary ripple sees `c` as its carry-in.  The Clifford frames turn it
into the signed contribution used by the square identity, avoiding a
controlled copy of the quantum addend. -/
def signedSquareRow (c : Wire) (xs dst pad carry : List Wire) : Program :=
  xorWhenFalse c (dst.take xs.length) ++
    addInPlace (xs ++ pad.take 1) dst (carry.take xs.length) c ++
    xorWhenFalse c dst

/-- Independent measured inverse of `signedSquareRow`; no measurement stream
is ever replayed backwards. -/
def signedSquareRowClear (c : Wire) (xs dst pad carry : List Wire) : Program :=
  xorWhenFalse c dst ++ (notRegister dst ++
    (addInPlace (xs ++ pad.take 1) dst (carry.take xs.length) c ++
      (notRegister dst ++ xorWhenFalse c (dst.take xs.length))))

/-- Low-to-high signed rows.  At recursion depth `i`, `dst` begins at product
bit `2i`; the active row is bits `2i+1 .. i+m`. -/
def signedSquareRows : List Wire → List Wire → List Wire → List Wire → Program
  | [], _, _, _ => []
  | _::[], _, _, _ => []
  | c::d::tail, dst, pad, carry =>
      signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry ++
        signedSquareRows (d::tail) (dst.drop 2) pad carry

/-- High-to-low independent cleanup of the signed rows. -/
def signedSquareRowsClear : List Wire → List Wire → List Wire → List Wire → Program
  | [], _, _, _ => []
  | _::[], _, _, _ => []
  | c::d::tail, dst, pad, carry =>
      signedSquareRowsClear (d::tail) (dst.drop 2) pad carry ++
        signedSquareRowClear c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry

/-- Copy the most significant input bit into the most significant product bit. -/
def signedSquareTop : List Wire → List Wire → Program
  | [], _ => []
  | [x], _::z::_ => [.CX x z]
  | _::x::xs, _::_::dst => signedSquareTop (x::xs) dst
  | _, _ => []

/-- Load `~xs[0..m-2]` into the low `m-1` mask wires. -/
def signedDiagLoad (xs mask : List Wire) (cin : Wire) : Program :=
  copyRegister none (xs.take (xs.length-1)) (mask.take (xs.length-1)) ++
    xorWhenFalse cin (mask.take (xs.length-1))

def signedDiagUnload (xs mask : List Wire) (cin : Wire) : Program :=
  xorWhenFalse cin (mask.take (xs.length-1)) ++
    copyRegister none (xs.take (xs.length-1)) (mask.take (xs.length-1))

/-- `xs ++ ~xs[0..m-2] ++ 0`, represented in `2m` wires. -/
def signedDiagSource (xs mask : List Wire) : List Wire := xs ++ mask.take xs.length

/-- Subtract the exact affine diagonal correction after all signed rows. -/
def signedDiagSub (xs dst mask carry : List Wire) (cin : Wire) : Program :=
  signedDiagLoad xs mask cin ++
    (subInPlace (signedDiagSource xs mask) dst (carry.take (dst.length-1)) cin ++
      signedDiagUnload xs mask cin)

def signedDiagAdd (xs dst mask carry : List Wire) (cin : Wire) : Program :=
  signedDiagLoad xs mask cin ++
    (addInPlace (signedDiagSource xs mask) dst (carry.take (dst.length-1)) cin ++
      signedDiagUnload xs mask cin)

/-- Exact square producer with signed rows and a single exact diagonal
correction.  The one-bit case is its direct Clifford square. -/
def signedTriangularSquare (xs dst pad mask carry : List Wire) (cin : Wire) : Program :=
  match xs, dst with
  | [], _ => []
  | [x], z::_ => [.CX x z]
  | _::_, _ => signedSquareRows xs dst pad carry ++
      (signedSquareTop xs dst ++ signedDiagSub xs dst mask carry cin)

/-- Independent exact cleanup of `signedTriangularSquare`. -/
def signedTriangularSquareClear (xs dst pad mask carry : List Wire) (cin : Wire) : Program :=
  match xs, dst with
  | [], _ => []
  | [x], z::_ => [.CX x z]
  | _::_, _ => signedDiagAdd xs dst mask carry cin ++
      (signedSquareTop xs dst ++ signedSquareRowsClear xs dst pad carry)

end ECDSAAdd.Arithmetic
