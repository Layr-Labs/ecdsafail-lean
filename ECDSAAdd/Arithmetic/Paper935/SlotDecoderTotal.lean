import ECDSAAdd.Arithmetic.Paper935.SlotDecoderCompiler
import ECDSAAdd.Arithmetic.Paper935.DepthListTotal
import ECDSAAdd.Arithmetic.Paper935.BankCompilerTotal

namespace ECDSAAdd.Arithmetic.Paper935

theorem compileSlotDecoder_exists (F : SlotRegisters) (Q : HistoricalSlot)
    (counter : F.counter.length=7)
    (distinct : ([F.one,F.frozen,Q.history.port]++F.counter++
      Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (owned : ([F.one,F.frozen,Q.history.port]++F.counter++
      Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.historyArena.live)
    (budget : Q.historyArena.live.card+
      rowGrowth (Q.slot.front.exitBank.requests Q.slot.front.exitBank.decoderWidth)+11≤935) :
    ∃ D,compileSlotDecoder F Q=some D := by
  let b := Q.slot.front.exitBank
  change Q.historyArena.live.card+rowGrowth (b.requests b.decoderWidth)+11≤935 at budget
  obtain ⟨C,out,p,hp,widths,geom,owns,card⟩ := compileBankResize_static_exists Q.historyArena b b.decoderWidth
    ([F.one,F.frozen,Q.history.port]++F.counter) distinct owned (by omega)
  have narrow : ([F.one,F.frozen,Q.history.port]++F.counter++out.f.wires++out.fv.wires).Nodup := by
    simp_all only [WindowBank.rows,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.nodup_append',List.disjoint_append_right,List.disjoint_append_left]
    tauto
  have narrowOwned : ([F.one,F.frozen,Q.history.port]++F.counter++out.f.wires++out.fv.wires).toFinset⊆C.live := by
    intro q hq
    apply owns
    simp only [List.mem_toFinset,List.mem_append,WindowBank.rows,List.flatMap_cons,List.flatMap_nil,List.mem_cons,
      List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hf : 7≤out.f.wires.length := by
    simp only [WindowRow.wires,List.length_append,List.length_singleton]
    have := widths.1
    dsimp only [WindowBank.decoderWidth] at this
    omega
  have hv : 13≤out.fv.wires.length := by
    simp only [WindowRow.wires,List.length_append,List.length_singleton]
    have := widths.2.2.1
    dsimp only [WindowBank.decoderWidth] at this
    omega
  obtain ⟨D,work,ls,hd⟩ := compileBorrowedDepths_exists C F.one F.frozen Q.history.port
    F.counter out.f.wires out.fv.wires counter hf hv narrow narrowOwned (by omega)
  exact ⟨⟨C,out,p,D,work,ls⟩,by simp [compileSlotDecoder,hp,hd,b]⟩

end ECDSAAdd.Arithmetic.Paper935
