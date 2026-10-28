import ECDSAAdd.Arithmetic.DivideResources

namespace ECDSAAdd.Arithmetic

namespace DivideLayout

def usedWires (L : DivideLayout) : List Wire :=
  L.control :: L.denominator ++ L.numerator ++ L.acc ++ L.inner.compactCoreWires

theorem multiply_used_subset (L : DivideLayout) (hw : L.Widths) :
    L.multiply.wires ⊆ L.usedWires := by
  intro q h
  have hb : [L.borrowedBit 0]++L.multiply.work ⊆ L.borrow := by
    rw [L.multiply_borrow hw]; exact (List.take_sublist _ _).subset
  change q∈L.inner.middle.r++L.numerator++(L.acc++[L.borrowedBit 0])++L.multiply.work at h
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
  have inner (hh : q∈L.inner.compactCoreWires) : q∈L.usedWires := by simp [usedWires,hh]
  rcases h with ((hr|hy)|(ho|he))|hw'
  · exact inner (L.inner.compact_reg_mem .r (by decide) hr)
  · simp [usedWires,hy]
  · simp [usedWires,ho]
  · exact inner (L.inner.compactBorrow_subset (hb (by simp [he])))
  · exact inner (L.inner.compactBorrow_subset (hb (List.mem_append_right _ hw')))

theorem data_used_subset (L : DivideLayout) (f : RoundField) (hf : f≠.out) :
    L.inner.first.data.reg f ⊆ L.inner.usedCoreWires := by
  intro q h
  have hm := L.inner.first.data.reg_used_mem f hf h
  simp only [InverseLoopLayout.usedCoreWires,KaliskiRoundLayout.usedRecordTapeWires,
    KaliskiRoundLayout.usedSharedWires,List.mem_append]
  tauto

theorem vLow_used_subset (L : DivideLayout) : L.vLow ⊆ L.inner.usedCoreWires := by
  intro q h
  apply L.data_used_subset .v (by decide)
  change q∈L.inverseView.inner.first.v
  rw [L.inverseView.v_split]
  exact List.mem_append_left _ h

theorem usedWires_nodup (L : DivideLayout) (hnd : L.wires.Nodup) : L.usedWires.Nodup := by
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp hnd q
  have hi : L.inner.compactCoreWires.count q ≤ L.inner.wires.count q := by
    have hh := (List.take_sublist 804 L.inner.arithmetic.wires).count_le q
    have hf := (L.inner.first.usedRecordTapeWires_sublist L.inner.records).count_le q
    simp only [InverseLoopLayout.compactCoreWires,InverseLoopLayout.compactBank,
      InverseLoopLayout.wires,InverseLoopLayout.extra,List.count_append]
    omega
  simp only [usedWires,wires,work,List.count_append,List.count_cons] at h ⊢
  omega

theorem old_core_subset (L : DivideLayout) (q : Wire) : q∈L.inner.usedCoreWires → q∈L.inner.compactCoreWires := by
  intro hh; rcases List.mem_append.mp hh with hh|hh
  · exact List.mem_append_left _ hh
  · exact List.mem_append_right _ ((List.take_sublist_take_left (by omega : 30≤804)).subset hh)
theorem compact_core_cover (L : DivideLayout) (hw : L.Widths) (q : Wire) : q∈L.inner.compactCoreWires → q∈L.inner.usedCoreWires ∨
    q∈L.multiply.x.take 256++L.multiply.y++L.multiply.out++L.multiply.work := by
  intro hh
  rcases List.mem_append.mp hh with hh|hh
  · exact Or.inl (List.mem_append_left _ hh)
  · right
    have hb : q∈L.borrow := by simp [DivideLayout.borrow,InverseLoopLayout.compactBorrow,hh]
    have he := L.multiply_borrow hw
    rw [List.take_of_length_le (by rw [L.borrow_length hw])] at he
    rw [←he] at hb
    rcases List.mem_append.mp hb with hb|hb
    · have hz : q∈L.multiply.out := List.mem_append_right _ hb
      simp only [List.mem_append]; exact Or.inl (Or.inr hz)
    · exact List.mem_append_right _ hb

end DivideLayout

/-- 静态支持是三外部寄存器、控制及求逆的实际核心；不含旧XOR输出银行。 -/
theorem divide_wires (L : DivideLayout) (hw : L.Widths) :
    wires (divideAdd L)=L.usedWires.toFinset ∧ wires (divideSub L)=L.usedWires.toFinset := by
  have hd : L.inner.first.data.width=257 := by
    simp [KaliskiRoundLayout.data,RoundDataLayout.width,show L.inner.first.low.length=256 from hw.inverse.low]
  have hi := inverseCompute_wires L.inner hw.inverse.records hw.inverse.counter (by omega)
    (by rw [hd,show L.inner.arithmetic.width=256 from hw.inverse.arithmetic])
    (by rw [show L.inner.a.length=257 from hw.inverse.a,show L.inner.arithmetic.width=256 from hw.inverse.arithmetic])
    (by rw [show L.inner.temp.length=257 from hw.inverse.temp,show L.inner.arithmetic.width=256 from hw.inverse.arithmetic]) hw.inverse.low hw.inverse.arithmetic p
  have hm := montControlledAdapter_wires L.control L.multiply p (L.multiply_widths hw)
  have hc := copyRegister_wires (some L.control) L.denominator L.vLow
    (hw.inverse.input.trans (L.vLow_length hw).symm)
  have hne : L.denominator.isEmpty=false := by
    cases he : L.denominator with
    | nil => have hh : L.denominator.length=256 := hw.inverse.input; simp [he] at hh
    | cons a as => rfl
  simp only [hne,Bool.false_eq_true,if_false,Option.toList_some,List.singleton_append] at hc
  have hvb : L.vBit∈L.inner.usedCoreWires := by
    apply L.vLow_used_subset
    have hh : L.vLow≠[] := by intro h; have hl := L.vLow_length hw; simp [h] at hl
    cases he : L.vLow with
    | nil => exact False.elim (hh he)
    | cons a as => simp [DivideLayout.vBit,he]
  have hu : wires (xorConstant L.inner.first.u p) ⊆ L.inner.usedCoreWires.toFinset := by
    intro q h
    exact List.mem_toFinset.mpr (L.data_used_subset .u (by decide) (List.mem_toFinset.mp (xorConstant_wires_subset _ _ h)))
  have hs : wires (xorConstant L.inner.first.s 1) ⊆ L.inner.usedCoreWires.toFinset := by
    intro q h
    exact List.mem_toFinset.mpr (L.data_used_subset .s (by decide) (List.mem_toFinset.mp (xorConstant_wires_subset _ _ h)))
  have heA : divideAdd L = divideLoad L ++ inverseCompute L.inner p ++
      (montMulControlledAdd L.control L.multiply p) ++
      inverseUncompute L.inner p ++ divideUnload L := by simp only [divideAdd,List.append_assoc]
  have heS : divideSub L = divideLoad L ++ inverseCompute L.inner p ++
      (montMulControlledSub L.control L.multiply p) ++
      inverseUncompute L.inner p ++ divideUnload L := by simp only [divideSub,List.append_assoc]
  have same : wires (divideAdd L)=wires (divideSub L) := by
    simp only [heA,heS,wires_append,hm.1,hm.2]
  suffices ha : wires (divideAdd L)=L.usedWires.toFinset from ⟨ha,same.symm.trans ha⟩
  rw [heA]
  simp only [wires_append,hi.1,hi.2,hm.1,divideLoad,divideUnload,wires_append,hc,
    wires,Instr.wires,Finset.union_empty]
  ext q
  have hu' := fun h => List.mem_toFinset.mp (hu (a:=q) h)
  have hs' := fun h => List.mem_toFinset.mp (hs (a:=q) h)
  have hv' := fun h => L.vLow_used_subset (a:=q) h
  have hm' : q∈L.multiply.x.take 256++L.multiply.y++L.multiply.out++L.multiply.work → q∈L.usedWires := by
    intro h
    apply L.multiply_used_subset hw
    have ht : q∈L.multiply.x.take 256 → q∈L.multiply.x := fun h => List.mem_of_mem_take h
    change q∈L.multiply.x++L.multiply.y++L.multiply.out++L.multiply.work
    simp only [List.mem_append] at h ⊢
    clear hw hd hi hm hc hne hu hs heA heS
    tauto
  have hn' : q∈L.numerator → q∈L.multiply.x.take 256++L.multiply.y++L.multiply.out++L.multiply.work := by intro h; simp [DivideLayout.multiply,borrowedMont,poolMul,h]
  have ha' : q∈L.acc → q∈L.multiply.x.take 256++L.multiply.y++L.multiply.out++L.multiply.work := by intro h; simp [DivideLayout.multiply,borrowedMont,poolMul,h]
  have oldnew := L.old_core_subset q
  have cover := L.compact_core_cover hw q
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,
    List.mem_cons,List.mem_append,DivideLayout.usedWires] at hm' hn' ha' cover ⊢
  clear hw hd hi hm hc hne hu hs heA heS
  grind only
/-- 精确3931根实际支持线；原分配布局及未执行的out银行不算作门列支持。 -/
theorem divide_qubits (L : DivideLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    qubitCount (divideAdd L)=3931 ∧ qubitCount (divideSub L)=3931 := by
  have hl := L.inner.compactCore_length hw.inverse.records hw.inverse.counter hw.inverse.low hw.inverse.arithmetic
  have hu : L.usedWires.length=3931 := by
    simp only [DivideLayout.usedWires,List.length_cons,List.length_append,
      show L.denominator.length=256 from hw.inverse.input,hw.numerator,hw.acc,hl]
  simp only [qubitCount,(divide_wires L hw).1,(divide_wires L hw).2,
    List.toFinset_card_of_nodup (L.usedWires_nodup hnd),hu,and_self]

end ECDSAAdd.Arithmetic
