import ECDSAAdd.Arithmetic.ControlledUnaryResources
import ECDSAAdd.Arithmetic.SwapLow

namespace ECDSAAdd.Arithmetic

namespace ModInPlaceLayout
/-- 回放的单目阶段借同一目标和零工作区。 -/
def unary (L : ModInPlaceLayout) : ModUnaryLayout :=
  ⟨L.low,L.high,L.constant,L.carry,L.cin,L.mask,L.flag⟩

theorem unary_widths (L : ModInPlaceLayout) (n : Nat) (h : L.Widths n) :
    L.unary.Widths n := ⟨h.core.low,h.core.constant,h.core.carry,h.mask⟩
end ModInPlaceLayout

/-- 两位记录只选择分支；活动位独立控制减半，00 不表示终止。 -/
def replayCell (active swap sub : Wire) (L : ModInPlaceLayout) (p : Nat) : Program :=
  swapRegisters swap (L.z.take L.low.length) (L.a.take L.low.length) ++
  controlledModSub sub L p ++ controlledHalf active L.unary p ++
  swapRegisters swap (L.z.take L.low.length) (L.a.take L.low.length)

/-- 前向门列组成的逆回放，不倒放测量。 -/
def replayUncell (active swap sub : Wire) (L : ModInPlaceLayout) (p : Nat) : Program :=
  swapRegisters swap (L.z.take L.low.length) (L.a.take L.low.length) ++
  controlledDouble active L.unary p ++ controlledModAdd sub L p ++
  swapRegisters swap (L.z.take L.low.length) (L.a.take L.low.length)

/-- 同一回放格的精确门数，包含首末两次低位交换。 -/
theorem replayCell_counts (active swap sub : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hnd : (sub::L.wires).Nodup) (hn : 0<n) :
    toffoliCount (replayCell active swap sub L p)=13*n+1 ∧
    measurementCount (replayCell active swap sub L p)=8*n-1 ∧
    toffoliCount (replayUncell active swap sub L p)=11*n-1 ∧
    measurementCount (replayUncell active swap sub L p)=6*n-2 := by
  have hz : L.z.length=n+1 := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low]
  have hl : (L.z.take L.low.length).length=n := by simp [hw.core.low,hz]
  have hr : (L.a.take L.low.length).length=n := by simp [hw.core.low,hw.core.a]
  have ca := copyRegister_counts (some swap) (L.z.take L.low.length)
    (L.a.take L.low.length) (hl.trans hr.symm)
  have cb := copyRegister_counts none (L.a.take L.low.length)
    (L.z.take L.low.length) (hr.trans hl.symm)
  have hs : toffoliCount (swapRegisters swap (L.z.take L.low.length) (L.a.take L.low.length))=n ∧
      measurementCount (swapRegisters swap (L.z.take L.low.length) (L.a.take L.low.length))=0 := by
    simp [swapRegisters,ca.1,ca.2,cb.1,cb.2,hl]
  have hm := controlledModSub_resources sub L n p hw hnd hn
  have ha := controlledModAdd_resources sub L n p hw hnd hn
  have hu := controlledUnary_counts active L.unary n p (L.unary_widths n hw) hn
  simp only [replayCell,replayUncell,toffoliCount_append,measurementCount_append,
    hs.1,hs.2,hm.1,hm.2.1,ha.1,ha.2.1,hu.1,hu.2.1,hu.2.2.1,hu.2.2.2]
  omega

end ECDSAAdd.Arithmetic
