import ECDSAAdd.Arithmetic.Paper935.DecoderProgramSupport
import ECDSAAdd.Arithmetic.Paper935.DecoderGeometry

namespace ECDSAAdd.Arithmetic.Paper935

private theorem zip_support (xs ws : List Wire) :
    ∀ q∈(List.zipWith ZeroBit.mk xs ws).flatMap ZeroBit.wires,q∈xs++ws := by
  induction xs generalizing ws with
  | nil => simp
  | cons x xs ih =>
    cases ws with
    | nil => simp
    | cons w ws =>
      intro q hq
      simp only [List.zipWith_cons_cons,List.flatMap_cons,ZeroBit.wires,List.cons_append,List.nil_append,
        List.mem_cons] at hq
      rcases hq with rfl|rfl|hq
      · simp
      · simp
      · have h := ih ws q hq
        simp only [List.mem_append,List.mem_cons] at h ⊢
        tauto

/-- Static geometry of the actual padding output, retaining all metadata and
history, is independent of quantum input values. -/
theorem compileSlotDecoder_geometry (F : SlotRegisters) (Q : HistoricalSlot) (D : SlotDecoder)
    (compiled : compileSlotDecoder F Q=some D)
    (distinct : (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.historyArena.live)
    (budget : Q.historyArena.live.card+rowGrowth (Q.slot.front.exitBank.requests Q.slot.front.exitBank.decoderWidth)≤935) :
    D.bank.Widths Q.slot.front.exitBank.decoderWidth ∧
    (F.wires++Q.history.record++D.bank.rows.flatMap WindowRow.wires).Nodup ∧
    (F.wires++Q.history.record++D.bank.rows.flatMap WindowRow.wires).toFinset⊆D.paddedArena.live := by
  obtain ⟨C,out,p,hp,widths,geom,owns,_⟩ := compileBankResize_static_exists Q.historyArena
    Q.slot.front.exitBank Q.slot.front.exitBank.decoderWidth (F.wires++Q.history.record) distinct owned budget
  rw [(compileSlotDecoder_contract F Q D compiled).1,Option.some.injEq,Prod.mk.injEq] at hp
  rcases hp with ⟨rfl,rfl,rfl⟩
  exact ⟨widths,geom,owns⟩

theorem compileSlotDecoder_program_support (F : SlotRegisters) (Q : HistoricalSlot) (D : SlotDecoder)
    (compiled : compileSlotDecoder F Q=some D) (port : Q.history.port=F.parity)
    (distinct : (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.historyArena.live)
    (budget : Q.historyArena.live.card+rowGrowth (Q.slot.front.exitBank.requests Q.slot.front.exitBank.decoderWidth)≤935)
    (p : Int) (index : Nat) : wires (D.program F Q p index)⊆arenaWires := by
  have layout := compileSlotDecoder_geometry F Q D compiled distinct owned budget
  have hc := compileSlotDecoder_contract F Q D compiled
  have borrow := (compileBorrowedDepths_contract _ _ _ _ _ _ _ _ _ _ hc.2).1
  have live := (D.paddedArena.borrowMany_live _ _ _ borrow).1
  have metadata (q : Wire) (hq : q∈F.wires) : q∈D.paddedArena.live :=
    layout.2.2 (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_append_left _ hq)))
  have row (q : Wire) (hq : q∈D.bank.rows.flatMap WindowRow.wires) : q∈D.paddedArena.live :=
    layout.2.2 (List.mem_toFinset.mpr (List.mem_append_right _ hq))
  have depthOwned : (F.one::F.frozen::Q.history.port::(F.counter++D.bank.f.wires++D.bank.fv.wires)).toFinset⊆D.paddedArena.live := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,port,or_assoc] at hq
    rcases hq with rfl|rfl|rfl|hq|hq|hq
    · exact metadata _ (by simp [SlotRegisters.wires])
    · exact metadata _ (by simp [SlotRegisters.wires])
    · exact metadata _ (by simp [SlotRegisters.wires])
    · exact metadata _ (by simp [SlotRegisters.wires,hq])
    · exact row _ (by simp [WindowBank.rows,hq])
    · exact row _ (by simp [WindowBank.rows,hq])
  have depth := (compileBorrowedDepths_support _ _ _ _ _ _ _ _ _ _ hc.2 depthOwned p).2.trans D.borrowedArena.bounded
  have padding := (compileBankResize_resources _ _ _ _ _ _ hc.1).2.2.2
  have work (q : Wire) (hq : q∈D.work) : q∈arenaWires := by
    apply D.borrowedArena.bounded
    rw [live]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr hq)
  have second : D.bank.fv.wires.getD 1 0∈arenaWires := by
    apply D.paddedArena.bounded
    apply row
    have len : 1<D.bank.fv.wires.length := by
      have h := layout.1.2.2.1
      simp only [WindowBank.decoderWidth] at h
      simp only [WindowRow.wires,List.length_append,List.length_singleton]
      omega
    have member : D.bank.fv.wires.getD 1 0∈D.bank.fv.wires := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem len,Option.getD_some]
      exact List.getElem_mem len
    simp only [WindowBank.rows,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_append]
    exact Or.inr (Or.inr (Or.inl member))
  apply paddedCleanBranch_support _ _ _ _ _ _ _ _ _ _ _ arenaWires padding depth
  intro q hq
  simp only [List.mem_toFinset,List.mem_cons,port] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|hq
  · exact D.paddedArena.bounded (metadata _ (by simp [SlotRegisters.wires]))
  · exact D.paddedArena.bounded (metadata _ (by simp [SlotRegisters.wires]))
  · exact D.paddedArena.bounded (metadata _ (by simp [SlotRegisters.wires]))
  · exact second
  · exact D.paddedArena.bounded (metadata _ (by simp [SlotRegisters.wires]))
  · exact D.paddedArena.bounded (metadata _ (by simp [SlotRegisters.wires]))
  · rcases List.mem_append.mp (zip_support F.offset D.work q hq) with h|h
    · exact D.paddedArena.bounded (metadata _ (by simp [SlotRegisters.wires,h]))
    · exact work q h

end ECDSAAdd.Arithmetic.Paper935
