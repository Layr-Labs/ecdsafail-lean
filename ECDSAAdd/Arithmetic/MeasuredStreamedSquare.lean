import ECDSAAdd.Arithmetic.CuccaroStreamedSquare
import ECDSAAdd.Arithmetic.MappedSignedSquare
import ECDSAAdd.Arithmetic.MeasuredCanonicalModProof
import ECDSAAdd.Arithmetic.MeasuredMaskedAdder

namespace ECDSAAdd.Arithmetic

structure MeasuredSquareFold where
  negative : Bool
  canonical : Bool
  src : List Wire
  shift : Nat := 0

namespace CuccaroStreamedSquareWideLayout

def inputBank (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 129
def leafCarry (L : CuccaroStreamedSquareWideLayout) : List Wire :=
  L.core.work.drop 129++(L.foldPad.drop 1).take 130
def leafPad (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldPad.take 1
def foldCarry (L : CuccaroStreamedSquareWideLayout) : List Wire :=
  L.foldPad++[L.core.productHigh,L.core.workHigh]
def shortCarry (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldCarry.take 255

def measuredCore (L : CuccaroStreamedSquareWideLayout) : MeasuredCanonicalModLayout :=
  {src:=L.core.work,out:=L.core.out,carry:=L.foldCarry,
    high:=L.core.outHigh,cin:=L.core.cin,flag:=L.core.modFlag}

def normalizeSource (L : CuccaroStreamedSquareWideLayout) : Program :=
  compareConstantGe L.core.work L.shortCarry L.core.cin L.core.normFlag SquareReduction.p++
    mappedConstAdd (some L.core.normFlag) L.core.work L.shortCarry L.core.cin SquareReduction.c

def restoreSource (L : CuccaroStreamedSquareWideLayout) : Program :=
  mappedConstAdd (some L.core.normFlag) L.core.work L.shortCarry L.core.cin SquareReduction.p++
    compareConstantGe L.core.work L.shortCarry L.core.cin L.core.normFlag SquareReduction.p

def reflectOutput (L : CuccaroStreamedSquareWideLayout) : Program :=
  notRegister L.core.out++mappedConstAdd none L.core.out L.shortCarry L.core.cin SquareReduction.p

def foldDestination (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold) : List Wire :=
  (L.core.work.drop f.shift).take f.src.length

def measuredFold (L : CuccaroStreamedSquareWideLayout) (f : MeasuredSquareFold) : Program :=
  copyRegister none f.src (L.foldDestination f)++
    (if f.canonical then [] else L.normalizeSource)++
    L.measuredCore.program SquareReduction.c SquareReduction.p++
    (if f.canonical then [] else L.restoreSource)++
    copyRegister none f.src (L.foldDestination f)

/-- The physical output is reflected only when the next signed term needs a
new orientation. No blanket quantum-control wrapper is applied to arithmetic. -/
def measuredFolds (L : CuccaroStreamedSquareWideLayout) : Bool → List MeasuredSquareFold → Program
  | _,[] => []
  | orientation,f::fs =>
      (if orientation=f.negative then [] else L.reflectOutput)++
        L.measuredFold f++L.measuredFolds f.negative fs

def nafMinusOneItems (negative : Bool) (src : List Wire) : List MeasuredSquareFold :=
  [{negative:=negative,canonical:=true,src:=src,shift:=4},
   {negative:=!negative,canonical:=true,src:=src,shift:=6},
   {negative:=negative,canonical:=true,src:=src,shift:=10},
   {negative:=negative,canonical:=true,src:=src,shift:=32}]

def measuredAItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  [{negative:=true,canonical:=true,src:=L.core.product.take 256},
   {negative:=false,canonical:=true,src:=L.rotated128}]++
    nafMinusOneItems false (L.core.product.drop 128)

def shiftedProductItems (negative : Bool) (src : List Wire) (j : Nat) : List MeasuredSquareFold :=
  if j=0 then [{negative:=negative,canonical:=true,src:=src}]
  else [{negative:=negative,canonical:=false,src:=rotateFull src j}]++
    nafMinusOneItems negative (src.drop (256-j))

def measuredBItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  [{negative:=false,canonical:=true,src:=L.rotated128}]++
    nafMinusOneItems false (L.core.product.drop 128)++
    shiftedProductItems true (L.core.product.take 256) 0++
    shiftedProductItems true (L.core.product.take 256) 4++
    shiftedProductItems false (L.core.product.take 256) 6++
    shiftedProductItems true (L.core.product.take 256) 10++
    shiftedProductItems true (L.core.product.take 256) 32

def measuredCItems (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold :=
  [{negative:=true,canonical:=true,src:=L.rotated128}]++
    nafMinusOneItems true (L.core.product.drop 128)++
    [{negative:=true,canonical:=true,src:=L.core.product.drop 256,shift:=128}]

/-- The input mask is measured out before folding, freeing the same work
register for source copies. It is recreated for the independent cleanup. -/
def withMeasuredSquare (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (src dst : List Wire) (body : Program) : Program :=
  copyRegister (some control) src (L.inputBank.take src.length)++
    mappedSignedSquare (L.inputBank.take src.length) dst L.leafPad L.leafCarry L.core.cin++
    eraseMask control src (L.inputBank.take src.length)++body++
    copyRegister (some control) src (L.inputBank.take src.length)++
    mappedSignedSquareClear (L.inputBank.take src.length) dst L.leafPad L.leafCarry L.core.cin++
    eraseMask control src (L.inputBank.take src.length)

def measuredBranchA (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.low (L.core.product.take 256)
    (L.measuredFolds false L.measuredAItems)
def measuredBranchB (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.withMeasuredSquare control L.core.high (L.core.product.take 256)
    (L.measuredFolds false L.measuredBItems)
def measuredBranchC (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.core.prepareSum++L.withMeasuredSquare control L.core.sum L.core.product
    (L.measuredFolds true L.measuredCItems)++L.core.clearSum

/-- Complete gate-level replacement of the controlled square stage. Its
resource and functional theorems are checked separately before promotion. -/
def measuredProgram (L : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  L.measuredBranchA control++L.measuredBranchB control++L.measuredBranchC control++L.reflectOutput

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
