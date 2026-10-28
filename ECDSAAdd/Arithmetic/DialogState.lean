import ECDSAAdd.Arithmetic.DialogRegisters

namespace ECDSAAdd.Arithmetic

/-- 值走终点的零工作字正好满足回放借用区，不要求载荷字清零。 -/
theorem DialogLayout.payload_work_zero (L : DialogLayout) (v : ValueState) (s : BasisState)
    (h : ValueLoopState L.first v s) : regValue L.payload.work s=0 := by
  have hy := (regValue_zero _ _).mp h.mask
  have hz := (regValue_zero _ _).mp h.zero
  have hc := (regValue_zero _ _).mp h.carry
  have hcy := (regValue_zero _ _).mp h.counterY
  have hcc := (regValue_zero _ _).mp h.counterCarry
  have hcl (w : Wire) (hw : w∈L.first.low.map (·.carry)) : s w=false := by
    apply hc
    simp only [KaliskiRoundLayout.data,RoundDataLayout.reg,List.map_append,List.map_cons,List.map_nil,List.mem_append]
    exact Or.inl hw
  have hch : s L.first.high.carry=false := hc _ (by
    simp [KaliskiRoundLayout.data,RoundDataLayout.reg,RoundBit.get])
  have hyt (w : Wire) (hw : w∈(L.first.data.reg .y).take 247) : s w=false :=
    hy _ (List.mem_of_mem_take hw)
  have hzt (w : Wire) (hw : w∈(L.first.data.reg .zero).take 247) : s w=false :=
    hz _ (List.mem_of_mem_take hw)
  rw [regValue_zero]
  intro w hw
  simp only [payload,ModInPlaceLayout.work,ModAddCoreLayout.work,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with ((((hw|hw)|hw)|hw)|(hw|hw))|hw
  · exact hyt _ hw
  · exact hcy _ hw
  · exact hcl _ hw
  · subst w; exact hch
  · exact hzt _ hw
  · exact hcc _ hw
  · subst w; exact h.odd

end ECDSAAdd.Arithmetic
