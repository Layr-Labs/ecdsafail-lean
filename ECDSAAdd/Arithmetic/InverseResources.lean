import ECDSAAdd.Arithmetic.InverseSpec

namespace ECDSAAdd.Arithmetic

/-- 装载/卸载的 CX/X 门不增加 Toffoli 或测量。 -/
theorem inverseLoad_counts (L : InverseLayout) (hw : L.Widths) :
    toffoliCount (inverseLoad L)=0 ∧ measurementCount (inverseLoad L)=0 ∧
    toffoliCount (inverseUnload L)=0 ∧ measurementCount (inverseUnload L)=0 := by
  have hc := copyRegister_counts none L.x L.vLow
    (by simp [InverseLayout.vLow,hw.input,hw.low])
  simp only [inverseLoad,inverseUnload,toffoliCount_append,measurementCount_append,
    hc.1,hc.2,(xorConstant_counts _ _).1,(xorConstant_counts _ _).2,
    Option.isSome_none,Bool.false_eq_true,if_false,Nat.zero_add,and_self]

def InverseLayout.usedWires (L : InverseLayout) : List Wire := L.x++L.inner.usedWires

theorem InverseLayout.usedWires_nodup (L : InverseLayout) (hn : L.wires.Nodup) :
    L.usedWires.Nodup :=
  (L.inner.usedWires_sublist.append_left L.x).nodup (L.wires_perm.nodup_iff.mp hn)

theorem InverseLayout.usedWires_subset (L : InverseLayout) : L.usedWires ⊆ L.wires := by
  intro w hw
  apply L.wires_perm.mem_iff.mpr
  exact (L.inner.usedWires_sublist.append_left L.x).subset hw

/-- 实际门列不触及第一阶段out银行；原分配工作区保持不变。 -/
theorem fieldInverse_wires (L : InverseLayout) (hw : L.Widths) :
    wires (fieldInverse L)=L.usedWires.toFinset := by
  have hi := inverseLoop_wires L.inner hw.records hw.counter
    (by simp [KaliskiRoundLayout.data,RoundDataLayout.width,hw.low])
    (by simp [KaliskiRoundLayout.data,RoundDataLayout.width,hw.low,hw.arithmetic])
    (by rw [hw.a,hw.arithmetic])
    (by rw [hw.temp,hw.arithmetic]) (by rw [hw.output,hw.arithmetic]) hw.low hw.arithmetic p
  have hc := copyRegister_wires none L.x L.vLow
    (by simp [InverseLayout.vLow,hw.input,hw.low])
  have hne : L.x.isEmpty=false := by
    cases hx : L.x with
    | nil => have hh := hw.input; rw [hx] at hh; contradiction
    | cons a as => rfl
  simp only [hne,Bool.false_eq_true,if_false,Option.toList_none,List.nil_append] at hc
  have hd (f : RoundField) (hf : f≠.out) {w : Wire} (h : w∈L.inner.first.data.reg f) :
      w∈L.usedWires := by
    have hm := L.inner.first.data.reg_used_mem f hf h
    simp only [InverseLayout.usedWires,InverseLoopLayout.usedWires,InverseLoopLayout.usedCoreWires,
      KaliskiRoundLayout.usedRecordTapeWires,KaliskiRoundLayout.usedSharedWires,List.mem_append]
    tauto
  have hu : wires (xorConstant L.inner.first.u p) ⊆ L.usedWires.toFinset := fun w h =>
    List.mem_toFinset.mpr (hd .u (by decide) (List.mem_toFinset.mp (xorConstant_wires_subset _ _ h)))
  have hs : wires (xorConstant L.inner.first.s 1) ⊆ L.usedWires.toFinset := fun w h =>
    List.mem_toFinset.mpr (hd .s (by decide) (List.mem_toFinset.mp (xorConstant_wires_subset _ _ h)))
  have hv : L.vLow ⊆ L.usedWires := by
    intro w h
    apply hd .v (by decide)
    change w∈L.inner.first.v
    rw [L.v_split]
    exact List.mem_append_left _ h
  rw [fieldInverse,inverseLoad,inverseUnload]
  simp only [wires_append,hi,hc]
  ext w
  have hu' : w∈wires (xorConstant L.inner.first.u p) → w∈L.usedWires :=
    fun h => List.mem_toFinset.mp (hu h)
  have hs' : w∈wires (xorConstant L.inner.first.s 1) → w∈L.usedWires :=
    fun h => List.mem_toFinset.mp (hs h)
  have hv' : w∈L.vLow → w∈L.usedWires := fun h => hv h
  simp only [InverseLayout.usedWires,List.mem_append] at hu' hs' hv'
  simp only [InverseLayout.usedWires,Finset.mem_union,List.mem_toFinset,List.mem_append]
  clear hi hc hne hu hs hv hd hw
  tauto

/-- 外部 256 位输入增加 256 根线路；原内核的输出高位仍计入工作区。 -/
theorem fieldInverse_resources (L : InverseLayout) (hnd : L.wires.Nodup) (hw : L.Widths) :
    toffoliCount (fieldInverse L)=3500551 ∧ measurementCount (fieldInverse L)=1918471 ∧
    qubitCount (fieldInverse L)=2901 := by
  have hi := inverseLoop_257_resources L.inner (L.inner_nodup hnd) hw.records hw.counter hw.low
    hw.arithmetic hw.a hw.temp hw.output p
  have hc := inverseLoad_counts L hw
  refine ⟨?_,?_,?_⟩
  · simp only [fieldInverse,toffoliCount_append,hc.1,hc.2.2.1,hi.1]
  · simp only [fieldInverse,measurementCount_append,hc.2.1,hc.2.2.2,hi.2.1]
  · have hwi := inverseLoop_wires L.inner hw.records hw.counter
      (by simp [KaliskiRoundLayout.data,RoundDataLayout.width,hw.low])
      (by simp [KaliskiRoundLayout.data,RoundDataLayout.width,hw.low,hw.arithmetic])
      (by rw [hw.a,hw.arithmetic])
      (by rw [hw.temp,hw.arithmetic]) (by rw [hw.output,hw.arithmetic]) hw.low hw.arithmetic p
    have hn := hi.2.2
    rw [qubitCount,hwi,List.toFinset_card_of_nodup (L.inner.usedWires_sublist.nodup (L.inner_nodup hnd))] at hn
    rw [qubitCount,fieldInverse_wires L hw,List.toFinset_card_of_nodup (L.usedWires_nodup hnd),InverseLayout.usedWires,
      List.length_append,hw.input,hn]

/-- 求逆接口的具体实现证明；正确性、精确资源和支持集均指向 fieldInverse L。 -/
theorem fieldInverse_contract (L : InverseLayout) (hnd : L.wires.Nodup) (hw : L.Widths) :
    inverseContract L.x L.out L.work (fieldInverse L) 3500551 1918471 2901 := by
  obtain ⟨ht,hm,hq⟩ := fieldInverse_resources L hnd hw
  refine ⟨hnd,hw.input,?_,fun X hX0 hX => fieldInverse_spec L hnd hw X hX0 hX,ht,hm,hq,?_⟩
  · simp [InverseLayout.out,hw.output]
  · rw [fieldInverse_wires L hw]
    exact fun _ h => List.mem_toFinset.mpr (L.usedWires_subset (List.mem_toFinset.mp h))

end ECDSAAdd.Arithmetic
