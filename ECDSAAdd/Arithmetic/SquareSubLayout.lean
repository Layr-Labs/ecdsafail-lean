import ECDSAAdd.Arithmetic.KaratsubaSquareResources
import ECDSAAdd.Arithmetic.SquareReduceResources
import ECDSAAdd.Arithmetic.ModInPlaceSubtract

namespace ECDSAAdd.Arithmetic

/-- 专用平方减法的共享区：和寄存器借 padding 后128位及独立最高位。
C 借 r 前258位；两个生命周期不重叠。 -/
structure SquareSubLayout where
  x : List Wire
  out : List Wire
  a : List Wire
  d : List Wire
  r : List Wire
  z : List Wire
  mask : List Wire
  carry : List Wire
  cin : Wire
  pad : List Wire
  b : Wire
  flag : Wire
  sourceHigh : Wire
  outputHigh : Wire
  constantHigh : Wire
  maskHigh : Wire
  layoutFlag : Wire
  sumHigh : Wire

namespace SquareSubLayout

def work (L : SquareSubLayout) := L.a++L.d++L.r++L.z++L.mask++L.carry++[L.cin]++L.pad++
  [L.b,L.flag,L.sourceHigh,L.outputHigh,L.constantHigh,L.maskHigh,L.layoutFlag,L.sumHigh]
def wires (L : SquareSubLayout) := L.x++L.out++L.work

structure Widths (L : SquareSubLayout) : Prop where
  x : L.x.length=256
  out : L.out.length=256
  a : L.a.length=256
  d : L.d.length=256
  r : L.r.length=289
  z : L.z.length=512
  mask : L.mask.length=256
  carry : L.carry.length=383
  pad : L.pad.length=256

def integer (L : SquareSubLayout) : KaratsubaSquareLayout :=
  { low := L.x.take 128, high := L.x.drop 128, a := L.a,d := L.d,c := L.r.take 258,
    z := L.z,sum := L.pad.drop 128++[L.sumHigh],pad := L.pad.take 128,
    mask := L.mask,carry := L.carry,cin := L.cin }

def reduction (L : SquareSubLayout) : SquareReduceLayout :=
  { low := L.z.take 256,high := L.z.drop 256,r := L.r,pad := L.pad,
    mask := L.mask,carry := L.carry,cin := L.cin,b := L.b,flag := L.flag }

def output (L : SquareSubLayout) : ModInPlaceLayout :=
  { toModAddCoreLayout := ⟨L.r.take 256++[L.sourceHigh],L.out,L.outputHigh,
      L.pad++[L.constantHigh],L.carry.take 256,L.cin⟩,
    mask := L.mask++[L.maskHigh],flag := L.layoutFlag }

theorem work_length (L : SquareSubLayout) (hw : L.Widths) : L.work.length=2217 := by
  simp [work,hw.a,hw.d,hw.r,hw.z,hw.mask,hw.carry,hw.pad]

theorem integer_valid (L : SquareSubLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.integer.Valid := by
  constructor
  · apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hn w
    have hx := congrArg (List.count w) (List.take_append_drop 128 L.x)
    have hp := congrArg (List.count w) (List.take_append_drop 128 L.pad)
    have hr := (List.take_sublist 258 L.r).count_le w
    simp only [wires,work,integer,KaratsubaSquareLayout.wires,List.count_append,
      List.count_cons,List.count_nil] at h hx hp ⊢
    omega
  all_goals simp [integer,hw.x,hw.a,hw.d,hw.r,hw.z,hw.pad,hw.mask,hw.carry]

theorem reduction_widths (L : SquareSubLayout) (hw : L.Widths) : L.reduction.Widths := by
  constructor <;> simp [reduction,hw.z,hw.r,hw.pad,hw.mask,hw.carry]

theorem reduction_nodup (L : SquareSubLayout) (hn : L.wires.Nodup) :
    L.reduction.wires.Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hn w
  have hz := congrArg (List.count w) (List.take_append_drop 256 L.z)
  simp only [wires,work,reduction,SquareReduceLayout.wires,List.count_append,
    List.count_cons,List.count_nil] at h hz ⊢
  omega

theorem output_widths (L : SquareSubLayout) (hw : L.Widths) : L.output.Widths 256 := by
  constructor
  · constructor <;> simp [output,hw.r,hw.out,hw.pad,hw.carry]
  · simp [output,hw.mask]

theorem output_nodup (L : SquareSubLayout) (hn : L.wires.Nodup) :
    L.output.wires.Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hn w
  have hr := (List.take_sublist 256 L.r).count_le w
  have hc := (List.take_sublist 256 L.carry).count_le w
  simp only [wires,work,output,ModInPlaceLayout.wires,ModInPlaceLayout.work,
    ModInPlaceLayout.z,ModAddCoreLayout.z,ModAddCoreLayout.work,
    List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

end SquareSubLayout

/-- 平方、三折叠、模减及完整恢复；所有历史跨过输出更新后才消去。 -/
def squareSub (L : SquareSubLayout) : Program :=
  karatsubaSquare L.integer ++ squareReduce L.reduction ++
  modSubInPlace L.output SquareReduction.p ++
  squareReduceClear L.reduction ++ karatsubaSquareClear L.integer

end ECDSAAdd.Arithmetic
