import ECDSAAdd.Arithmetic.TriangularSquareSpec

namespace ECDSAAdd.Arithmetic

/-- Integer-square layout. All fields denote disjoint physical registers. -/
structure KaratsubaSquareLayout where
  low : List Wire
  high : List Wire
  a : List Wire
  d : List Wire
  c : List Wire
  z : List Wire
  sum : List Wire
  pad : List Wire
  mask : List Wire
  carry : List Wire
  cin : Wire

namespace KaratsubaSquareLayout

def wires (L : KaratsubaSquareLayout) : List Wire :=
  L.cin :: (L.low++L.high++L.a++L.d++L.c++L.z++L.sum++L.pad++L.mask++L.carry)

structure Valid (L : KaratsubaSquareLayout) : Prop where
  nodup : L.wires.Nodup
  low_length : L.low.length=128
  high_length : L.high.length=128
  a_length : L.a.length=256
  d_length : L.d.length=256
  c_length : L.c.length=258
  z_length : L.z.length=512
  sum_length : L.sum.length=129
  pad_length : L.pad.length=128
  mask_length : L.mask.length=256
  carry_length : L.carry.length=383

/-- Form the 129-bit sum; the one padding bit remains zero. -/
def prepareSum (L : KaratsubaSquareLayout) : Program :=
  copyRegister none L.low (L.sum.take 128) ++
    addInPlace (L.high++L.pad.take 1) L.sum (L.carry.take 128) L.cin

def clearSum (L : KaratsubaSquareLayout) : Program :=
  subInPlace (L.high++L.pad.take 1) L.sum (L.carry.take 128) L.cin ++
    copyRegister none L.low (L.sum.take 128)

def squareLow (L : KaratsubaSquareLayout) : Program :=
  triangularSquare L.low L.a L.pad L.mask L.carry L.cin

def clearLow (L : KaratsubaSquareLayout) : Program :=
  triangularSquareClear L.low L.a L.pad L.mask L.carry L.cin

def squareHigh (L : KaratsubaSquareLayout) : Program :=
  triangularSquare L.high L.d L.pad L.mask L.carry L.cin

def clearHigh (L : KaratsubaSquareLayout) : Program :=
  triangularSquareClear L.high L.d L.pad L.mask L.carry L.cin

def squareSum (L : KaratsubaSquareLayout) : Program :=
  triangularSquare L.sum L.c L.pad L.mask L.carry L.cin

def clearSquareSum (L : KaratsubaSquareLayout) : Program :=
  triangularSquareClear L.sum L.c L.pad L.mask L.carry L.cin

/-- Copy the disjoint low/high square words into the zero 512-bit result. -/
def copySquares (L : KaratsubaSquareLayout) : Program :=
  copyRegister none L.a (L.z.take 256) ++ copyRegister none L.d (L.z.drop 256)

/-- The cross term is added at offset 128, with full 384-bit propagation. -/
def combine (L : KaratsubaSquareLayout) : Program :=
  addInPlace (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin ++
  subInPlace (L.a++L.pad) (L.z.drop 128) L.carry L.cin ++
  subInPlace (L.d++L.pad) (L.z.drop 128) L.carry L.cin

def uncombine (L : KaratsubaSquareLayout) : Program :=
  addInPlace (L.d++L.pad) (L.z.drop 128) L.carry L.cin ++
  addInPlace (L.a++L.pad) (L.z.drop 128) L.carry L.cin ++
  subInPlace (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin

end KaratsubaSquareLayout

/-- Compute the full square, retaining the two half-squares A and D. -/
def karatsubaSquare (L : KaratsubaSquareLayout) : Program :=
  L.squareLow ++ L.squareHigh ++ L.prepareSum ++ L.squareSum ++ L.clearSum ++
  L.copySquares ++ L.combine ++ L.prepareSum ++ L.clearSquareSum ++ L.clearSum

/-- Independent forward cleanup: reconstruct C before undoing the cross term. -/
def karatsubaSquareClear (L : KaratsubaSquareLayout) : Program :=
  L.prepareSum ++ L.squareSum ++ L.clearSum ++ L.uncombine ++ L.copySquares ++
  L.prepareSum ++ L.clearSquareSum ++ L.clearSum ++ L.clearHigh ++ L.clearLow

end ECDSAAdd.Arithmetic
