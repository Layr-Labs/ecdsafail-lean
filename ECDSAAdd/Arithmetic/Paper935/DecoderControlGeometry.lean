import ECDSAAdd.Arithmetic.Paper935.DecoderPoolReuse

namespace ECDSAAdd.Arithmetic.Paper935

structure SlotDecoder.ControlGeometry (D : SlotDecoder) (F : SlotRegisters) (Q : HistoricalSlot) : Prop where
  core : [F.frozen,F.work0,F.work1,D.bank.fv.wires.getD 1 0,F.swap,Q.history.port].Nodup
  compare : (F.frozen::F.work0::(List.zipWith ZeroBit.mk F.offset D.work).flatMap ZeroBit.wires).Nodup
  portCompare : Q.history.port∉F.frozen::F.work0::(List.zipWith ZeroBit.mk F.offset D.work).flatMap ZeroBit.wires
  owned : ∀ q∈[F.work0,F.work1,F.swap],q∈D.paddedArena.live
  away : ∀ q∈F.one::F.frozen::(F.counter++D.bank.rows.flatMap WindowRow.wires),
    q≠F.work0 ∧ q≠F.work1 ∧ q≠F.swap

theorem compileSlotDecoder_control_geometry (F : SlotRegisters) (Q : HistoricalSlot) (D : SlotDecoder)
    (compiled : compileSlotDecoder F Q=some D) (port : Q.history.port=F.parity)
    (distinct : (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.historyArena.live)
    (budget : Q.historyArena.live.card+rowGrowth (Q.slot.front.exitBank.requests Q.slot.front.exitBank.decoderWidth)≤935) :
    D.ControlGeometry F Q := by
  have layout := compileSlotDecoder_geometry F Q D compiled distinct owned budget
  have borrow := (compileBorrowedDepths_contract _ _ _ _ _ _ _ _ _ _
    (compileSlotDecoder_contract F Q D compiled).2).1
  have allgeom := D.paddedArena.borrowMany_append _ _ _ _ borrow layout.2.1 layout.2.2
  have selected (xs : List Wire)
      (counts : ∀ q,xs.count q≤((F.wires++Q.history.record++D.bank.rows.flatMap WindowRow.wires)++D.work).count q) :
      xs.Nodup := List.nodup_iff_count.mpr (fun q => (counts q).trans (List.nodup_iff_count.mp allgeom.1 q))
  have secondMem : D.bank.fv.wires.getD 1 0∈D.bank.rows.flatMap WindowRow.wires := by
    have len : 1<D.bank.fv.wires.length := by
      have h := layout.1.2.2.1
      simp only [WindowBank.decoderWidth] at h
      simp only [WindowRow.wires,List.length_append,List.length_singleton]
      omega
    have member : D.bank.fv.wires.getD 1 0∈D.bank.fv.wires := by
      rw [List.getD_eq_getElem _ _ len]
      exact List.getElem_mem len
    simp only [WindowBank.rows,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_append]
    exact Or.inr (Or.inr (Or.inl member))
  have secondCount (q : Wire) : (if D.bank.fv.wires.getD 1 0=q then 1 else 0)≤
      (D.bank.rows.flatMap WindowRow.wires).count q := by
    split
    next h => subst q; exact List.count_pos_iff.mpr secondMem
    next h => omega
  have core : [F.frozen,F.work0,F.work1,D.bank.fv.wires.getD 1 0,F.swap,Q.history.port].Nodup := by
    apply selected
    intro q
    have h := secondCount q
    simp only [SlotRegisters.wires,List.count_append,List.count_cons,List.count_nil,port,beq_iff_eq]
    omega
  have comparison : ([F.frozen,F.work0]++(F.offset++D.work)).Nodup := by
    apply selected
    intro q
    simp only [SlotRegisters.wires,List.count_append,List.count_cons,List.count_nil]
    omega
  have separated : ([F.work0,F.work1,F.swap]++(F.one::F.frozen::(F.counter++D.bank.rows.flatMap WindowRow.wires))).Nodup := by
    apply selected
    intro q
    simp only [SlotRegisters.wires,List.count_append,List.count_cons,List.count_nil]
    omega
  have comparisonFull : ([Q.history.port,F.frozen,F.work0]++(F.offset++D.work)).Nodup := by
    apply selected
    intro q
    simp only [SlotRegisters.wires,List.count_append,List.count_cons,List.count_nil,port]
    omega
  have cp := zeroViews_prefixed_distinct [Q.history.port,F.frozen,F.work0] F.offset D.work comparisonFull
  refine ⟨core,zeroViews_prefixed_distinct [F.frozen,F.work0] F.offset D.work comparison,
    (List.nodup_cons.mp cp).1,?_,?_⟩
  · intro q hq
    apply layout.2.2
    simp only [List.mem_toFinset,List.mem_append]
    apply Or.inl
    apply Or.inl
    simp only [SlotRegisters.wires,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    tauto
  · intro q hq
    have sep := (List.nodup_append'.mp separated).2.2
    refine ⟨?_,?_,?_⟩ <;> intro he
    · exact List.disjoint_left.mp sep (by simp [he]) hq
    · exact List.disjoint_left.mp sep (by simp [he]) hq
    · exact List.disjoint_left.mp sep (by simp [he]) hq

end ECDSAAdd.Arithmetic.Paper935
