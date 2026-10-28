import ECDSAAdd.Arithmetic.InverseLoopResources
import ECDSAAdd.Arithmetic.InverseContract

namespace ECDSAAdd.Arithmetic

/-- 外部输入另占 256 位；内核输出的末位作为工作位，公开输出取其低 256 位。 -/
structure InverseLayout where
  inner : InverseLoopLayout
  x : List Wire

namespace InverseLayout

def out (L : InverseLayout) : List Wire := L.inner.out.take 256
def vLow (L : InverseLayout) : List Wire := L.inner.first.low.map RoundBit.v
def rest (L : InverseLayout) : List Wire :=
  L.inner.first.r ++ L.inner.first.k ++ [L.inner.first.done] ++ L.inner.work ++
    [L.inner.first.high.v] ++ L.inner.out.drop 256
def work (L : InverseLayout) : List Wire :=
  L.inner.first.u ++ L.vLow ++ L.inner.first.s ++ L.rest
def wires (L : InverseLayout) : List Wire := L.x ++ L.out ++ L.work

structure Widths (L : InverseLayout) : Prop where
  input : L.x.length=256
  records : L.inner.records.length=512
  counter : L.inner.first.counter.width=10
  low : L.inner.first.low.length=256
  arithmetic : L.inner.arithmetic.width=256
  a : L.inner.a.length=257
  temp : L.inner.temp.length=257
  output : L.inner.out.length=257

theorem v_split (L : InverseLayout) : L.inner.first.v=L.vLow++[L.inner.first.high.v] := by
  simp [KaliskiRoundLayout.v,KaliskiRoundLayout.data,RoundDataLayout.v,RoundDataLayout.reg,
    RoundBit.get,vLow]

private theorem data_count (bs : List RoundBit) (w : Wire) :
    (bs.flatMap RoundBit.wires).count w =
    (bs.map RoundBit.u).count w + (bs.map RoundBit.v).count w +
    (bs.map RoundBit.r).count w + (bs.map RoundBit.s).count w +
    (bs.map RoundBit.y).count w + (bs.map RoundBit.out).count w +
    (bs.map RoundBit.carry).count w + (bs.map RoundBit.zero).count w := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons,RoundBit.wires,List.map_cons,List.count_append,
      List.count_cons,List.count_nil,ih]
    omega

private theorem counter_count (bs : List AddBit) (w : Wire) :
    (addWires bs).count w =
    (bs.map AddBit.x).count w + (bs.map AddBit.y).count w +
    (bs.map AddBit.out).count w + (bs.map AddBit.carry).count w := by
  induction bs with
  | nil => simp [addWires]
  | cons b bs ih => simp only [addWires,List.map_cons,List.count_cons,ih]; omega

theorem wires_perm (L : InverseLayout) : L.wires.Perm (L.x++L.inner.wires) := by
  apply List.perm_iff_count.mpr
  intro w
  have ho := congrArg (List.count w) (List.take_append_drop 256 L.inner.out)
  simp only [List.count_append] at ho
  simp only [wires,out,work,rest,vLow,InverseLoopLayout.wires,InverseLoopLayout.work,
    KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,KaliskiRoundLayout.scratch,
    KaliskiRoundLayout.u,KaliskiRoundLayout.r,KaliskiRoundLayout.s,
    KaliskiRoundLayout.k,KaliskiRoundLayout.kNext,KaliskiRoundLayout.data,KaliskiRoundLayout.counter,
    RoundDataLayout.u,RoundDataLayout.r,RoundDataLayout.s,RoundDataLayout.work,
    RoundDataLayout.reg,RoundDataLayout.wires,AdderLayout.wires,AdderLayout.x,AdderLayout.y,
    AdderLayout.out,AdderLayout.carry,List.count_append,List.count_cons,List.count_nil,
    data_count,counter_count,List.map_append,List.map_cons,List.map_nil,RoundBit.get]
  simp only [(show (fun b : RoundBit => b.u) = RoundBit.u from rfl),
    (show (fun b : RoundBit => b.r) = RoundBit.r from rfl),
    (show (fun b : RoundBit => b.s) = RoundBit.s from rfl),
    (show (fun b : RoundBit => b.y) = RoundBit.y from rfl),
    (show (fun b : RoundBit => b.out) = RoundBit.out from rfl),
    (show (fun b : RoundBit => b.carry) = RoundBit.carry from rfl),
    (show (fun b : RoundBit => b.zero) = RoundBit.zero from rfl)]
  omega

theorem inner_nodup (L : InverseLayout) (hnd : L.wires.Nodup) : L.inner.wires.Nodup :=
  (List.nodup_append'.mp (L.wires_perm.nodup_iff.mp hnd)).2.1

end InverseLayout

/-- 装入外部输入及常数；卸载使用同样的 XOR 门，按相反次序执行。 -/
def inverseLoad (L : InverseLayout) : Program :=
  copyRegister none L.x L.vLow ++ xorConstant L.inner.first.u p ++ xorConstant L.inner.first.s 1

def inverseUnload (L : InverseLayout) : Program :=
  xorConstant L.inner.first.s 1 ++ xorConstant L.inner.first.u p ++ copyRegister none L.x L.vLow

/-- secp256k1 非零输入的具体求逆电路。 -/
def fieldInverse (L : InverseLayout) : Program :=
  inverseLoad L ++ inverseLoop L.inner p ++ inverseUnload L

end ECDSAAdd.Arithmetic
