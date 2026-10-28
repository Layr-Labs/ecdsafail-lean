import ECDSAAdd.Arithmetic.InverseLoopSpec

namespace ECDSAAdd.Arithmetic

/-- 同一字面门列的精确资源；w 为带额外高位的数据宽度；512正/逆轮加一次缩放准备/恢复。 -/
theorem inverseLoop_resources (L : InverseLoopLayout) (hnd : L.wires.Nodup)
    (hn : L.records.length=512) (hw : L.first.counter.width=10) (hd : 2≤L.first.data.width)
    (hwidth : L.first.data.width=L.arithmetic.width+1)
    (ha : L.a.length=L.arithmetic.width+1)
    (ht : L.temp.length=L.arithmetic.width+1) (hout : L.out.length=L.arithmetic.width+1)
    (hlow : L.first.low.length=256) (harith : L.arithmetic.width=256) (q : Nat) :
    toffoliCount (inverseLoop L q)=512*(24*L.first.data.width+63)+1535+308744 ∧
    measurementCount (inverseLoop L q)=512*(12*L.first.data.width+57)+1535+308744 ∧
    qubitCount (inverseLoop L q)=8*L.first.data.width+589 := by
  have hfirst := oneBitRecordLoop_counts L.first L.records 0 (L.first_nodup hnd) hw
  have hrlen : L.middle.r.length=L.arithmetic.width+1 := by
    change (L.middle.data.reg .r).length=_
    rw [L.middle.data.reg_length,InverseLoopLayout.middle,loopEnd_data,hwidth]
  have hneg := negativeEven_counts L.compactNeg 256 q (L.compactNeg_widths harith hlow) (by omega)
  have hscale := L.compactScaling.counts q (L.compactScaling_widths (by omega) harith hlow hw)
  have hc := terminalConstants_resources L q
  have hcopy := copyRegister_counts none L.middle.r L.out (hrlen.trans hout.symm)
  refine ⟨?_,?_,?_⟩
  · simp only [inverseLoop,inverseCompute,inverseUncompute,toffoliCount_append,
      hfirst.1,hfirst.2.2.1,hneg.1,hneg.2.2.1,hc.1,hscale.1.1,hscale.2.1,hcopy.1,
      Option.isSome_none,Bool.false_eq_true,if_false,hn]
    omega
  · simp only [inverseLoop,inverseCompute,inverseUncompute,measurementCount_append,
      hfirst.2.1,hfirst.2.2.2,hneg.2.1,hneg.2.2.2,hc.2.1,hscale.1.2,hscale.2.2,hcopy.2,hn]
    omega
  · rw [qubitCount,inverseLoop_wires L hn hw hd hwidth ha ht hout hlow harith q,List.toFinset_card_of_nodup (L.usedWires_sublist.nodup hnd)]
    have hne : L.records≠[] := by intro h; rw [h] at hn; simp at hn
    have hbits := oneBitRecordLoop_qubits L.first L.records 0 (L.first_nodup hnd) hw hd hne
    have hwire := oneBitRecordLoop_wires L.first L.records 0 hw hd
    have hempty : L.records.isEmpty=false := by cases he : L.records with
      | nil => exact False.elim (hne he)
      | cons r rs => rfl
    simp only [qubitCount,hwire.1,hempty,Bool.false_eq_true,if_false,
      List.toFinset_card_of_nodup ((L.first.usedRecordTapeWires_sublist L.records).nodup (L.first_nodup hnd)),hn] at hbits
    have hm (bs : List ModBit) : (bs.flatMap ModBit.all).length=8*bs.length := by
      induction bs with
      | nil => rfl
      | cons b bs ih => simp [ModBit.all,ih]; omega
    have hl : L.arithmetic.wires.length=8*(L.arithmetic.width+1)+2 := by
      simp [ModLayout.wires,ModLayout.bits,ModLayout.width,hm,ModBit.all]
      omega
    simp only [InverseLoopLayout.usedWires,InverseLoopLayout.usedCoreWires,List.length_append,List.length_take,hout,hl]
    omega

/-- 257 位内部数据、512 轮的当前实现；计数银行、512 根减法记录与一根共享交换线和第二阶段工作区均计入。 -/
theorem inverseLoop_257_resources (L : InverseLoopLayout) (hnd : L.wires.Nodup)
    (hn : L.records.length=512) (hw : L.first.counter.width=10)
    (hlow : L.first.low.length=256) (harith : L.arithmetic.width=256)
    (ha : L.a.length=257) (ht : L.temp.length=257) (hout : L.out.length=257) (q : Nat) :
    toffoliCount (inverseLoop L q)=3500551 ∧ measurementCount (inverseLoop L q)=1918471 ∧
    qubitCount (inverseLoop L q)=2645 := by
  have hd : L.first.data.width=257 := by simp [KaliskiRoundLayout.data,RoundDataLayout.width,hlow]
  simpa only [hd] using inverseLoop_resources L hnd hn hw (by omega) (by omega)
    (by omega) (by omega) (by omega) hlow harith q

end ECDSAAdd.Arithmetic
