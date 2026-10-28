import ECDSAAdd.Arithmetic.ValueBoundary
import ECDSAAdd.Arithmetic.ReplayLoopResources
import ECDSAAdd.Arithmetic.DialogReplayMath

namespace ECDSAAdd.Arithmetic

/-- 值走旧视图的r/s/out现在分别是X+g、Y、Z，均在值走支持之外。 -/
structure DialogLayout where
  first : KaliskiRoundLayout
  records : List RoundRecord

namespace DialogLayout

def control (L : DialogLayout) : Wire := L.first.high.r
def x (L : DialogLayout) : List Wire := L.first.low.map (·.r)
def y (L : DialogLayout) : List Wire := L.first.s
def z (L : DialogLayout) : List Wire := L.first.data.reg .out
def work (L : DialogLayout) : List Wire := L.first.valueTapeWires L.records ++ L.z
def wires (L : DialogLayout) : List Wire := L.first.tapeWires L.records

structure Widths (L : DialogLayout) : Prop where
  low : L.first.low.length=256
  counter : L.first.counter.width=10
  records : L.records.length=512

/-- 比较器借用原计数器y/carry；把它们嵌入载荷零工作区，避免新字。
剩余247位来自值走mask/zero，算术cin取carry高位，flag取oddWork。 -/
def payload (L : DialogLayout) : ModInPlaceLayout :=
  { a := L.z, low := L.first.low.map (·.s), high := L.first.high.s,
    constant := (L.first.data.reg .y).take 247 ++ L.first.counter.y,
    carry := L.first.low.map (·.carry), cin := L.first.high.carry,
    mask := (L.first.data.reg .zero).take 247 ++ L.first.counter.carry,
    flag := L.first.oddWork }

def replay (L : DialogLayout) : ReplayLayout :=
  ⟨L.payload,{ L.first.counter with cin := L.first.high.carry },L.first.active⟩

theorem payload_fields (L : DialogLayout) : L.payload.z=L.y ∧ L.payload.a=L.z := by
  constructor
  · simp [payload,ModInPlaceLayout.z,ModAddCoreLayout.z,y,KaliskiRoundLayout.s,
      KaliskiRoundLayout.data,RoundDataLayout.s,RoundDataLayout.reg,RoundBit.get]
  · rfl

theorem payload_widths (L : DialogLayout) (hw : L.Widths) : L.payload.Widths 256 := by
  have hc : L.first.counter.bits.length=10 := hw.counter
  constructor
  · constructor <;>
      simp [payload,z,hw.low,KaliskiRoundLayout.data,RoundDataLayout.reg,AdderLayout.y,List.length_take,hc]
  · simp [payload,hw.low,KaliskiRoundLayout.data,RoundDataLayout.reg,AdderLayout.carry,List.length_take,hc]

end DialogLayout

private theorem swapCounter_twice (L : KaliskiRoundLayout) : L.swapCounter.swapCounter=L := by
  cases L
  simp [KaliskiRoundLayout.swapCounter,List.map_map,Function.comp_def]

/-- 偶数轮恢复计数银行方向，512轮无需额外交换银行。 -/
theorem valueEnd_even (L : KaliskiRoundLayout) (n : Nat) : loopEndLayout L (2*n)=L := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,loopEndLayout,loopEndLayout,swapCounter_twice,ih]

end ECDSAAdd.Arithmetic
