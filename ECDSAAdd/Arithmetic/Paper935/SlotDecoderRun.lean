import ECDSAAdd.Arithmetic.Paper935.SlotDecoderCoreRun

namespace ECDSAAdd.Arithmetic.Paper935

theorem compileSlotDecoder_run (F : SlotRegisters) (Q : HistoricalSlot) (D : SlotDecoder)
    (compiled : compileSlotDecoder F Q=some D) (port : Q.history.port=F.parity)
    (distinct : (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.historyArena.live)
    (budget : Q.historyArena.live.card+rowGrowth (Q.slot.front.exitBank.requests Q.slot.front.exitBank.decoderWidth)≤935)
    (offsetWidth : F.offset.length=6) (index : Nat) (indexBound : index<533)
    (p : Int) (st : ECDSAAdd.Divsteps.ZState) (inv : ECDSAAdd.Divsteps.Inv p st) (odd : p%2=1)
    (oldFrozen armed : Bool) (r : Nat) (oldOffset : r<decoderOffset index)
    (frozenZero : oldFrozen=true → st.g=0)
    (firstZero : oldFrozen=false → armed=true → (ECDSAAdd.Divsteps.zStep st).g=0 → st.g≠0)
    (s : State) (m : List Bool) (ready : Q.historyArena.Ready s.basis)
    (one : s.basis F.one=true) (fire : s.basis F.work0=false)
    (active : s.basis F.work1=false) (sigma : s.basis F.swap=false)
    (rows : Q.slot.front.exitBank.Encodes s.basis (if oldFrozen then st else ECDSAAdd.Divsteps.zStep st))
    (counter : signedRegValue F.counter s.basis=(if oldFrozen then st else ECDSAAdd.Divsteps.zStep st).z)
    (frozen : s.basis F.frozen=(oldFrozen || (!oldFrozen && armed && decide ((ECDSAAdd.Divsteps.zStep st).g=0))))
    (record : regValue F.offset s.basis=(if !oldFrozen && armed && decide ((ECDSAAdd.Divsteps.zStep st).g=0)
      then decoderOffset index else r)) :
    let stored := !(oldFrozen || (!oldFrozen && armed && decide ((ECDSAAdd.Divsteps.zStep st).g=0))) &&
      decide ((ECDSAAdd.Divsteps.zStep st).z≤0) && decide ((2:Int)^7∣(ECDSAAdd.Divsteps.zStep st).fv)
    run (D.program F Q p index) m s=
      ⟨s.phase,writeBit s.basis Q.history.port (s.basis Q.history.port ^^ (!stored && decide (ECDSAAdd.Divsteps.bbit st=1)))⟩ := by
  let bank := Q.slot.front.exitBank
  have hc := (compileSlotDecoder_contract F Q D compiled).1
  have plan := compileBankResize_contract Q.historyArena D.paddedArena bank D.bank bank.decoderWidth D.padding hc
  have pad := bank.resize_resources D.bank bank.decoderWidth Q.historyArena D.paddedArena D.padding plan
  have result := bank.resize_correct D.bank bank.decoderWidth Q.historyArena D.paddedArena D.padding plan s m
    (if oldFrozen then st else ECDSAAdd.Divsteps.zStep st) ready rows
    (bank.decoderWidth_fits s.basis _ rows)
  have metaOwned (q : Wire) (hq : q∈F.wires) : q∈Q.historyArena.live :=
    owned (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_append_left _ hq)))
  have metaAway (q : Wire) (hq : q∈F.wires) : q∉bank.rows.flatMap WindowRow.wires := by
    intro hrow
    exact List.disjoint_left.mp (List.nodup_append'.mp distinct).2.2 (List.mem_append_left _ hq) hrow
  have keep (q : Wire) (hq : q∈F.wires) : (run D.padding m s).basis q=s.basis q :=
    (result.2.2.2.2 q (metaOwned q hq) (metaAway q hq)).2
  have core := compileSlotDecoder_core_run F Q D compiled port distinct owned budget offsetWidth index indexBound
    p st inv odd oldFrozen armed r oldOffset frozenZero firstZero (run D.padding m s) m result.2.1
    ((keep F.one (by simp [SlotRegisters.wires])).trans one)
    ((keep F.work0 (by simp [SlotRegisters.wires])).trans fire)
    ((keep F.work1 (by simp [SlotRegisters.wires])).trans active)
    ((keep F.swap (by simp [SlotRegisters.wires])).trans sigma) result.2.2.1
    (by
      unfold signedRegValue
      rw [regValue_congr F.counter (run D.padding m s).basis s.basis
        (fun q hq => keep q (by simp [SlotRegisters.wires,hq]))]
      exact counter)
    ((keep F.frozen (by simp [SlotRegisters.wires])).trans frozen)
    (by
      rw [regValue_congr F.offset (run D.padding m s).basis s.basis
        (fun q hq => keep q (by simp [SlotRegisters.wires,hq]))]
      exact record)
  have portMeta : Q.history.port∈F.wires := by rw [port]; simp [SlotRegisters.wires]
  have away := bank.padding_support_away D.bank bank.decoderWidth Q.historyArena D.paddedArena
    D.padding plan Q.history.port (metaOwned _ portMeta) (metaAway _ portMeta)
  dsimp only at core ⊢
  rw [SlotDecoder.program,paddedCleanBranch,run_append,run_take,pad.2.2.1,List.drop_zero,
    run_append,run_take,core,decoder_unpad D.padding pad.1 Q.history.port away s m,
    FiniteUnitary.run_phase D.padding pad.1,keep Q.history.port portMeta]

end ECDSAAdd.Arithmetic.Paper935
