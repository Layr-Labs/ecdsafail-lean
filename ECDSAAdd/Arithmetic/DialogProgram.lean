import ECDSAAdd.Arithmetic.DialogLayoutProof
import ECDSAAdd.Arithmetic.SafeDivisor
import ECDSAAdd.Arithmetic.SwapRegisters
import ECDSAAdd.Arithmetic.Constant

namespace ECDSAAdd.Arithmetic

/-- XOR装卸安全分母；高位仍为零。空低字只是定义的总化分支。 -/
def dialogLoad (L : DialogLayout) (p : Nat) : Program :=
  xorConstant L.first.u p ++
    match L.first.low.map (·.v) with
    | [] => []
    | h::t => safeDivisor L.control L.x h t

/-- 先把(Y,0)交换为(0,Y)，再沿值走记录正向回放。 -/
def dialogDivide (L : DialogLayout) (p : Nat) : Program :=
  dialogLoad L p ++ valueLoop L.first 0 L.records ++
    exchangeRegisters L.y L.z ++ replayLoop L.replay p 0 L.records ++
    valueUnloop L.first 0 L.records ++ dialogLoad L p

/-- 逆向回放把(Y,0)变成(0,XY)，最后交换回固定输出字。 -/
def dialogMultiply (L : DialogLayout) (p : Nat) : Program :=
  dialogLoad L p ++ valueLoop L.first 0 L.records ++
    replayUnloop L.replay p 0 L.records ++ exchangeRegisters L.y L.z ++
    valueUnloop L.first 0 L.records ++ dialogLoad L p

theorem dialogLoad_counts (L : DialogLayout) (p : Nat) (hw : L.Widths) :
    toffoliCount (dialogLoad L p)=256 ∧ measurementCount (dialogLoad L p)=0 := by
  have hl : (L.first.low.map (·.v)).length=256 := by simp [hw.low]
  have hx : L.x.length=256 := by simp [DialogLayout.x,hw.low]
  unfold dialogLoad
  split
  · simp_all
  · rename_i h t he
    have ht : L.x.length=(h::t).length := by rw [← he,hx,hl]
    have hc := safeDivisor_counts L.control L.x h t ht
    simp only [toffoliCount_append,measurementCount_append,(xorConstant_counts _ _).1,
      (xorConstant_counts _ _).2,Nat.zero_add,hc.1,hc.2,hx]
    simp

/-- 完整生成/恢复、安全分母装卸及活动比较均包含在这两条门列中。 -/
theorem dialog_counts (L : DialogLayout) (p : Nat) (hw : L.Widths) (hn : L.wires.Nodup) :
    toffoliCount (dialogDivide L p)=3130638 ∧ measurementCount (dialogDivide L p)=1877512 ∧
    toffoliCount (dialogMultiply L p)=2867470 ∧ measurementCount (dialogMultiply L p)=1614856 := by
  have hd : L.first.data.width=257 := by
    simp [KaliskiRoundLayout.data,RoundDataLayout.width,hw.low]
  have hv := valueLoop_counts L.first L.records 0 hn hw.counter (by omega)
  rw [hd,hw.records,valueWidthSum_257] at hv
  have hr := replay512_counts L.replay p L.records (L.replay_valid hw hn) hw.records
  have hl := dialogLoad_counts L p hw
  have hyz : L.y.length=L.z.length := by
    simp [DialogLayout.y,DialogLayout.z,KaliskiRoundLayout.s,RoundDataLayout.s,RoundDataLayout.reg]
  have h1 := copyRegister_counts none L.y L.z hyz
  have h2 := copyRegister_counts none L.z L.y hyz.symm
  have hs : toffoliCount (exchangeRegisters L.y L.z)=0 ∧
      measurementCount (exchangeRegisters L.y L.z)=0 := by
    simp [exchangeRegisters,toffoliCount_append,measurementCount_append,h1.1,h1.2,h2.1,h2.2]
  simp only [dialogDivide,dialogMultiply,toffoliCount_append,measurementCount_append,
    hl.1,hl.2,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,hs.1,hs.2]
  simp

end ECDSAAdd.Arithmetic
