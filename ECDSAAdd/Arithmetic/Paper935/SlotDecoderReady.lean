import ECDSAAdd.Arithmetic.Paper935.DecoderControlGeometry

namespace ECDSAAdd.Arithmetic.Paper935

/-- The real slot decoder reuses its eleven borrowed wires for offset
comparison and all five depth lookups. Static control separation is derived
from the compiled layout; only actual state values remain as inputs. -/
theorem compileSlotDecoder_after_mint (F : SlotRegisters) (Q : HistoricalSlot) (D : SlotDecoder)
    (compiled : compileSlotDecoder F Q=some D) (port : Q.history.port=F.parity)
    (distinct : (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.historyArena.live)
    (budget : Q.historyArena.live.card+rowGrowth (Q.slot.front.exitBank.requests Q.slot.front.exitBank.decoderWidth)≤935)
    (offsetWidth : F.offset.length=6) (index : Nat) (indexBound : index<533)
    (st : ECDSAAdd.Divsteps.ZState) (s : State) (m : List Bool)
    (ready : D.paddedArena.Ready s.basis) (one : s.basis F.one=true)
    (fire : s.basis F.work0=false) (active : s.basis F.work1=false) (sigma : s.basis F.swap=false)
    (rows : s.basis F.frozen=false → D.bank.Encodes s.basis (ECDSAAdd.Divsteps.zStep st))
    (counter : s.basis F.frozen=false → signedRegValue F.counter s.basis=(ECDSAAdd.Divsteps.zStep st).z) :
    let t := run (mintHistoryControls F.frozen F.work0 F.work1 (D.bank.fv.wires.getD 1 0) F.swap
      (List.zipWith ZeroBit.mk F.offset D.work) (decoderOffset index)) m s
    D.paddedArena.Ready t.basis ∧ (∀ q∈D.work,t.basis q=false) ∧ ∀ L∈D.layouts,L.Available st t := by
  have geometry := compileSlotDecoder_control_geometry F Q D compiled port distinct owned budget
  have core : [F.frozen,F.work0,F.work1,D.bank.fv.wires.getD 1 0,F.swap].Nodup :=
    List.Nodup.of_append_left (l₂ := [Q.history.port]) (by
      simpa only [List.cons_append,List.nil_append] using geometry.core)
  have len : (List.zipWith ZeroBit.mk F.offset D.work).length=6 := by
    simp only [List.length_zipWith,offsetWidth,(compileSlotDecoder_pool F Q D compiled).1]
    decide
  have fits : decoderOffset index<2^(List.zipWith ZeroBit.mk F.offset D.work).length := by
    rw [len]
    simp only [decoderOffset]
    omega
  exact compileBorrowedDepths_after_mint D.paddedArena D.borrowedArena F.one F.frozen Q.history.port
    D.bank F.counter D.work D.layouts (compileSlotDecoder_contract F Q D compiled).2
    F.work0 F.work1 (D.bank.fv.wires.getD 1 0) F.swap F.offset (decoderOffset index)
    core geometry.compare fits geometry.owned geometry.away st s m ready one fire active sigma rows counter

end ECDSAAdd.Arithmetic.Paper935
