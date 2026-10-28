import ECDSAAdd.Arithmetic.CuccaroSignedSquareResources
import ECDSAAdd.Arithmetic.CuccaroNormalizedModProof
import ECDSAAdd.Arithmetic.SquareFold
import ECDSAAdd.Math.SquareReduction

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic

/-- Exact low-width workspace for a `with_square` schedule.  `product` holds
only the currently active Karatsuba leaf.  `work` is reused as the signed
square mask while the leaf is built and as modular scratch while it is folded. -/
structure CuccaroStreamedSquareLayout where
  y : List Wire
  out : List Wire
  product : List Wire
  pad : List Wire
  work : List Wire
  productHigh : Wire
  outHigh : Wire
  workHigh : Wire
  cin : Wire
  normFlag : Wire
  modFlag : Wire
  sumCarry : Wire

namespace CuccaroStreamedSquareLayout

def wires (L : CuccaroStreamedSquareLayout) : List Wire :=
  L.y++L.out++L.product++L.pad++L.work++
    [L.productHigh,L.outHigh,L.workHigh,L.cin,L.normFlag,L.modFlag,L.sumCarry]

structure Widths (L : CuccaroStreamedSquareLayout) : Prop where
  y : L.y.length=256
  out : L.out.length=256
  product : L.product.length=258
  pad : L.pad.length=128
  work : L.work.length=256

def low (L : CuccaroStreamedSquareLayout) : List Wire := L.y.take 128
def high (L : CuccaroStreamedSquareLayout) : List Wire := (L.y.drop 128).take 128
def sum (L : CuccaroStreamedSquareLayout) : List Wire := L.high++[L.sumCarry]

def square128 (L : CuccaroStreamedSquareLayout) (src : List Wire) : Program :=
  cuccaroSignedTriangularSquare src (L.product.take 256) L.pad
    (L.work.take 128) [] L.cin

def square128Clear (L : CuccaroStreamedSquareLayout) (src : List Wire) : Program :=
  cuccaroSignedTriangularSquareClear src (L.product.take 256) L.pad
    (L.work.take 128) [] L.cin

def square129 (L : CuccaroStreamedSquareLayout) : Program :=
  cuccaroSignedTriangularSquare L.sum L.product L.pad
    (L.work.take 129) [] L.cin

def square129Clear (L : CuccaroStreamedSquareLayout) : Program :=
  cuccaroSignedTriangularSquareClear L.sum L.product L.pad
    (L.work.take 129) [] L.cin

def prepareSum (L : CuccaroStreamedSquareLayout) : Program :=
  cuccaroAdd (L.low++[L.pad.getD 0 0]) L.sum L.cin

def clearSum (L : CuccaroStreamedSquareLayout) : Program := L.prepareSum.reverse

theorem low_length (L : CuccaroStreamedSquareLayout) (hw : L.Widths) :
    L.low.length=128 := by simp [low,hw.y]

theorem high_length (L : CuccaroStreamedSquareLayout) (hw : L.Widths) :
    L.high.length=128 := by simp [high,hw.y]

theorem sum_length (L : CuccaroStreamedSquareLayout) (hw : L.Widths) :
    L.sum.length=129 := by simp [sum,L.high_length hw]

/-- Exact producer prices before fold fusion.  The destination is cleaned by
the inverse before the next producer is materialized. -/
theorem square128_counts (L : CuccaroStreamedSquareLayout) (hw : L.Widths)
    (src : List Wire) (hs : src.length=128) :
    (toffoliCount (L.square128 src)=16766 ∧ measurementCount (L.square128 src)=0) ∧
    (toffoliCount (L.square128Clear src)=16766 ∧
      measurementCount (L.square128Clear src)=0) := by
  simpa [square128,square128Clear] using
    cuccaroSignedTriangularSquare_counts_128 src (L.product.take 256) L.pad
      (L.work.take 128) [] L.cin hs (by simp [hw.product])
      (by simp [hw.pad]) (by simp [hw.work])

theorem square129_counts (L : CuccaroStreamedSquareLayout) (hw : L.Widths) :
    (toffoliCount L.square129=17026 ∧ measurementCount L.square129=0) ∧
    (toffoliCount L.square129Clear=17026 ∧ measurementCount L.square129Clear=0) := by
  simpa [square129,square129Clear] using
    cuccaroSignedTriangularSquare_counts_129 L.sum L.product L.pad
      (L.work.take 129) [] L.cin (L.sum_length hw) hw.product
      (by simp [hw.pad]) (by simp [hw.work])

theorem sum_counts (L : CuccaroStreamedSquareLayout) (hw : L.Widths) :
    (toffoliCount L.prepareSum=256 ∧ measurementCount L.prepareSum=0) ∧
    (toffoliCount L.clearSum=256 ∧ measurementCount L.clearSum=0) := by
  have h := cuccaroAdd_counts (L.low++[L.pad.getD 0 0]) L.sum L.cin (by
    simp [L.low_length hw,L.sum_length hw])
  constructor
  · constructor
    · change toffoliCount (cuccaroAdd (L.low++[L.pad.getD 0 0]) L.sum L.cin)=256
      rw [h.1,L.sum_length hw]
    · simpa [prepareSum] using h.2
  · rw [clearSum,toffoliCount_reverse,measurementCount_reverse]
    constructor
    · change toffoliCount (cuccaroAdd (L.low++[L.pad.getD 0 0]) L.sum L.cin)=256
      rw [h.1,L.sum_length hw]
    · simpa [prepareSum] using h.2

/-- Static support of the streamed workspace itself.  A concrete point layout
adds its resident point and classification wires to this pool. -/
theorem wires_length (L : CuccaroStreamedSquareLayout) (hw : L.Widths) :
    L.wires.length=1161 := by
  simp [wires,hw.y,hw.out,hw.product,hw.pad,hw.work]

end CuccaroStreamedSquareLayout

/-- Provisional exact fold layout.  The extra 126 clean sites make every
short NAF source, including the two-bit cross-term overhang at shift 128,
an explicit 256-bit word.  They are the only sites that must disappear to
move the executable version from 1,296 Q to the 1,170-Q core envelope. -/
structure CuccaroStreamedSquareWideLayout where
  core : CuccaroStreamedSquareLayout
  overflowPad : List Wire

namespace CuccaroStreamedSquareWideLayout

def wires (L : CuccaroStreamedSquareWideLayout) : List Wire :=
  L.core.wires++L.overflowPad

structure Widths (L : CuccaroStreamedSquareWideLayout) : Prop where
  core : L.core.Widths
  overflowPad : L.overflowPad.length=126

def foldPad (L : CuccaroStreamedSquareWideLayout) : List Wire :=
  L.core.pad++L.overflowPad

def source (L : CuccaroStreamedSquareWideLayout) (src : List Wire) :
    CuccaroNormalizedModLayout :=
  { src:=src,srcHigh:=L.core.productHigh,out:=L.core.out,outHigh:=L.core.outHigh,
    work:=L.core.work,workHigh:=L.core.workHigh,cin:=L.core.cin,
    normFlag:=L.core.normFlag,modFlag:=L.core.modFlag }

def shifted (L : CuccaroStreamedSquareWideLayout) (src : List Wire) (j : Nat) : List Wire :=
  shiftedSource src L.foldPad j 256

def addSource (L : CuccaroStreamedSquareWideLayout) (src : List Wire) : Program :=
  cuccaroNormalizedModAdd (L.source src) SquareReduction.c SquareReduction.p

def subSource (L : CuccaroStreamedSquareWideLayout) (src : List Wire) : Program :=
  cuccaroNormalizedModSub (L.source src) SquareReduction.c SquareReduction.p

/-- Add `(c-1)*high` in its exact four-term NAF. -/
def addCMinusOne (L : CuccaroStreamedSquareWideLayout) (high : List Wire) : Program :=
  L.addSource (L.shifted high 4)++L.subSource (L.shifted high 6)++
    L.addSource (L.shifted high 10)++L.addSource (L.shifted high 32)

def subCMinusOne (L : CuccaroStreamedSquareWideLayout) (high : List Wire) : Program :=
  L.subSource (L.shifted high 4)++L.addSource (L.shifted high 6)++
    L.subSource (L.shifted high 10)++L.subSource (L.shifted high 32)

def rotated128 (L : CuccaroStreamedSquareWideLayout) : List Wire :=
  (L.core.product.drop 128).take 128++L.core.product.take 128

/-- Add/subtract the 128-bit rotate.  The 258-bit sum-square has a two-bit
unit-term overhang; `withOverhang` includes its exact correction at shift 128. -/
def addRotate128 (L : CuccaroStreamedSquareWideLayout) (withOverhang : Bool) : Program :=
  L.addSource L.rotated128++L.addCMinusOne (L.core.product.drop 128)++
    if withOverhang then L.addSource (L.shifted (L.core.product.drop 256) 128) else []

def subRotate128 (L : CuccaroStreamedSquareWideLayout) (withOverhang : Bool) : Program :=
  L.subSource L.rotated128++L.subCMinusOne (L.core.product.drop 128)++
    if withOverhang then L.subSource (L.shifted (L.core.product.drop 256) 128) else []

def rotateFull (src : List Wire) (j : Nat) : List Wire :=
  src.drop (256-j)++src.take (256-j)

def addShiftFull (L : CuccaroStreamedSquareWideLayout) (src : List Wire) (j : Nat) : Program :=
  if j=0 then L.addSource src
  else L.addSource (rotateFull src j)++L.addCMinusOne (src.drop (256-j))

def subShiftFull (L : CuccaroStreamedSquareWideLayout) (src : List Wire) (j : Nat) : Program :=
  if j=0 then L.subSource src
  else L.subSource (rotateFull src j)++L.subCMinusOne (src.drop (256-j))

/-- Exact five-term NAF multiplication by `c`. -/
def subTimesC (L : CuccaroStreamedSquareWideLayout) (src : List Wire) : Program :=
  L.subShiftFull src 0++L.subShiftFull src 4++L.addShiftFull src 6++
    L.subShiftFull src 10++L.subShiftFull src 32

def branchA (L : CuccaroStreamedSquareWideLayout) : Program :=
  L.core.square128 L.core.low++
  L.subSource (L.core.product.take 256)++L.addRotate128 false++
  L.core.square128Clear L.core.low

def branchB (L : CuccaroStreamedSquareWideLayout) : Program :=
  (L.core.square128 L.core.high++L.addRotate128 false)++
    (L.subTimesC (L.core.product.take 256)++L.core.square128Clear L.core.high)

def branchC (L : CuccaroStreamedSquareWideLayout) : Program :=
  L.core.prepareSum++
    (L.core.square129++L.subRotate128 true++L.core.square129Clear)++
    L.core.clearSum

/-- Executable exact `with_square` schedule for `out -= y^2 (mod p)`. -/
def program (L : CuccaroStreamedSquareWideLayout) : Program :=
  L.branchA++L.branchB++L.branchC

theorem foldPad_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]

theorem source_widths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (src : List Wire) (hs : src.length=256) : (L.source src).Widths 256 :=
  ⟨hs,hw.core.out,hw.core.work⟩

theorem shifted_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (src : List Wire) (j : Nat) (hs0 : 2≤src.length) (hs : src.length+j≤256) :
    (L.shifted src j).length=256 := by
  apply shiftedSource_length
  · omega
  · rw [L.foldPad_length hw]
    omega

theorem rotateFull_length (src : List Wire) (j : Nat)
    (hs : src.length=256) (hj : j≤256) : (rotateFull src j).length=256 := by
  simp [rotateFull,hs]

theorem wires_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.wires.length=1287 := by
  simp [wires,L.core.wires_length hw.core,hw.overflowPad]

private theorem addSource_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (src : List Wire) (hs : src.length=256) :
    toffoliCount (L.addSource src)=4602 ∧ measurementCount (L.addSource src)=0 := by
  simpa [addSource] using cuccaroNormalizedModAdd_counts (L.source src) 256
    SquareReduction.c SquareReduction.p (L.source_widths hw src hs)

private theorem subSource_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (src : List Wire) (hs : src.length=256) :
    toffoliCount (L.subSource src)=5114 ∧ measurementCount (L.subSource src)=0 := by
  simpa [subSource] using cuccaroNormalizedModSub_counts (L.source src) 256
    SquareReduction.c SquareReduction.p (L.source_widths hw src hs)

theorem cMinusOne_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (high : List Wire) (hlo : 2≤high.length) (hhi : high.length+32≤256) :
    (toffoliCount (L.addCMinusOne high)=18920 ∧
      measurementCount (L.addCMinusOne high)=0) ∧
    (toffoliCount (L.subCMinusOne high)=19944 ∧
      measurementCount (L.subCMinusOne high)=0) := by
  have s4 := L.shifted_length hw high 4 hlo (by omega)
  have s6 := L.shifted_length hw high 6 hlo (by omega)
  have s10 := L.shifted_length hw high 10 hlo (by omega)
  have s32 := L.shifted_length hw high 32 hlo hhi
  have a4 := L.addSource_counts hw _ s4
  have a6 := L.addSource_counts hw _ s6
  have a10 := L.addSource_counts hw _ s10
  have a32 := L.addSource_counts hw _ s32
  have s4c := L.subSource_counts hw _ s4
  have s6c := L.subSource_counts hw _ s6
  have s10c := L.subSource_counts hw _ s10
  have s32c := L.subSource_counts hw _ s32
  simp [addCMinusOne,subCMinusOne,toffoliCount_append,measurementCount_append,
    a4.1,a4.2,a6.1,a6.2,a10.1,a10.2,a32.1,a32.2,
    s4c.1,s4c.2,s6c.1,s6c.2,s10c.1,s10c.2,s32c.1,s32c.2]

theorem rotate128_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (toffoliCount (L.addRotate128 false)=23522 ∧
      measurementCount (L.addRotate128 false)=0) ∧
    (toffoliCount (L.subRotate128 false)=25058 ∧
      measurementCount (L.subRotate128 false)=0) ∧
    (toffoliCount (L.subRotate128 true)=30172 ∧
      measurementCount (L.subRotate128 true)=0) := by
  have hr : L.rotated128.length=256 := by simp [rotated128,hw.core.product]
  have hh : (L.core.product.drop 128).length=130 := by simp [hw.core.product]
  have ho : (L.core.product.drop 256).length=2 := by simp [hw.core.product]
  have hs : (L.shifted (L.core.product.drop 256) 128).length=256 :=
    L.shifted_length hw _ _ (by omega) (by omega)
  have ra := L.addSource_counts hw _ hr
  have rs := L.subSource_counts hw _ hr
  have cs := L.cMinusOne_counts hw (L.core.product.drop 128) (by omega) (by omega)
  have os := L.subSource_counts hw _ hs
  simp [addRotate128,subRotate128,toffoliCount_append,measurementCount_append,
    ra.1,ra.2,rs.1,rs.2,cs.1.1,cs.1.2,cs.2.1,cs.2.2,os.1,os.2]

theorem shiftFull_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (src : List Wire) (hs : src.length=256) (j : Nat) (hj0 : 2≤j) (hj : j≤224) :
    (toffoliCount (L.addShiftFull src j)=23522 ∧
      measurementCount (L.addShiftFull src j)=0) ∧
    (toffoliCount (L.subShiftFull src j)=25058 ∧
      measurementCount (L.subShiftFull src j)=0) := by
  have jn : j≠0 := by omega
  have hr := rotateFull_length src j hs (by omega)
  have hh : (src.drop (256-j)).length=j := by simp [hs]; omega
  have cm := L.cMinusOne_counts hw (src.drop (256-j)) (by omega) (by omega)
  have ra := L.addSource_counts hw _ hr
  have rs := L.subSource_counts hw _ hr
  simp [addShiftFull,subShiftFull,jn,toffoliCount_append,measurementCount_append,
    ra.1,ra.2,rs.1,rs.2,cm.1.1,cm.1.2,cm.2.1,cm.2.2]

theorem subTimesC_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (src : List Wire) (hs : src.length=256) :
    toffoliCount (L.subTimesC src)=103810 ∧ measurementCount (L.subTimesC src)=0 := by
  have d := L.subSource_counts hw src hs
  have f4 := (L.shiftFull_counts hw src hs 4 (by omega) (by omega)).2
  have f6 := (L.shiftFull_counts hw src hs 6 (by omega) (by omega)).1
  have f10 := (L.shiftFull_counts hw src hs 10 (by omega) (by omega)).2
  have f32 := (L.shiftFull_counts hw src hs 32 (by omega) (by omega)).2
  have z : L.subShiftFull src 0=L.subSource src := by simp [subShiftFull]
  simp [subTimesC,z,d.1,d.2,
    toffoliCount_append,measurementCount_append,
    f4.1,f4.2,f6.1,f6.2,f10.1,f10.2,f32.1,f32.2]

theorem program_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount L.program=287768 ∧ measurementCount L.program=0 := by
  have lo := L.core.square128_counts hw.core L.core.low (L.core.low_length hw.core)
  have hi := L.core.square128_counts hw.core L.core.high (L.core.high_length hw.core)
  have su := L.core.square129_counts hw.core
  have sm := L.core.sum_counts hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have ds := L.subSource_counts hw _ p256
  have rot := L.rotate128_counts hw
  have fc := L.subTimesC_counts hw _ p256
  simp [program,branchA,branchB,branchC,toffoliCount_append,measurementCount_append,
    lo.1.1,lo.1.2,lo.2.1,lo.2.2,hi.1.1,hi.1.2,hi.2.1,hi.2.2,
    su.1.1,su.1.2,su.2.1,su.2.2,sm.1.1,sm.1.2,sm.2.1,sm.2.2,
    ds.1,ds.2,rot.1.1,rot.1.2,rot.2.1.1,rot.2.1.2,rot.2.2.1,rot.2.2.2,
    fc.1,fc.2]

end CuccaroStreamedSquareWideLayout

/-- The exact five-term non-adjacent form used by the incumbent fold. -/
theorem secp256k1_c_naf :
    SquareReduction.c+2^6=2^32+2^10+2^4+1 := by
  norm_num [SquareReduction.c]

/-- Rotating a product by 128 bits can be folded without materializing a
fresh 256-bit word.  The low 128-bit limb is rotated into the high half and
the remaining limb is multiplied by the pseudo-Mersenne constant.  This is
valid for the 258-bit cross-term as well as the two 256-bit leaves. -/
theorem rotate128_fold_exact (P : Nat) :
    (((P%2^128)*2^128)+SquareReduction.c*(P/2^128))%SquareReduction.p=
      (P*2^128)%SquareReduction.p := by
  have h := SquareReduction.first_mod ((P%2^128)*2^128) (P/2^128)
  have split : (P%2^128)*2^128+SquareReduction.B*(P/2^128)=P*2^128 := by
    rw [SquareReduction.B]
    have hp := Nat.mod_add_div P (2^128)
    nlinarith
  calc
    (((P%2^128)*2^128)+SquareReduction.c*(P/2^128))%SquareReduction.p =
        (((P%2^128)*2^128)+SquareReduction.B*(P/2^128))%SquareReduction.p := h
    _ = (P*2^128)%SquareReduction.p := by rw [split]

/-- The 258-bit sum-square leaves only a 130-bit quotient after the rotate.
Consequently `c` times that quotient fits in 163 bits, which removes the
extra 256-bit temporary from the earlier design. -/
theorem cross_high130_bound (P : Nat) (hP : P<2^258) :
    P/2^128<2^130 := by
  exact (Nat.div_lt_iff_lt_mul (by positivity : 0<2^128)).2 (by
    simpa [←Nat.pow_add] using hP)

theorem cross_fold_term_bound (P : Nat) (hP : P<2^258) :
    SquareReduction.c*(P/2^128)<2^163 := by
  have hh := cross_high130_bound P hP
  norm_num [SquareReduction.c] at *
  nlinarith

end ECDSAAdd.Arithmetic
