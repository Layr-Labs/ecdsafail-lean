import ECDSAAdd.Arithmetic.Paper935.DecoderCleanup

namespace ECDSAAdd.Arithmetic.Paper935

theorem compileSlotDecoder_core_run (F : SlotRegisters) (Q : HistoricalSlot) (D : SlotDecoder)
    (compiled : compileSlotDecoder F Q=some D) (port : Q.history.port=F.parity)
    (distinct : (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++Q.history.record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.historyArena.live)
    (budget : Q.historyArena.live.card+rowGrowth (Q.slot.front.exitBank.requests Q.slot.front.exitBank.decoderWidth)≤935)
    (offsetWidth : F.offset.length=6) (index : Nat) (indexBound : index<533)
    (p : Int) (st : ECDSAAdd.Divsteps.ZState) (inv : ECDSAAdd.Divsteps.Inv p st) (odd : p%2=1)
    (oldFrozen armed : Bool) (r : Nat) (oldOffset : r<decoderOffset index)
    (frozenZero : oldFrozen=true → st.g=0)
    (firstZero : oldFrozen=false → armed=true → (ECDSAAdd.Divsteps.zStep st).g=0 → st.g≠0)
    (s : State) (m : List Bool) (ready : D.paddedArena.Ready s.basis)
    (one : s.basis F.one=true) (fire : s.basis F.work0=false)
    (active : s.basis F.work1=false) (sigma : s.basis F.swap=false)
    (rows : D.bank.Encodes s.basis (if oldFrozen then st else ECDSAAdd.Divsteps.zStep st))
    (counter : signedRegValue F.counter s.basis=(if oldFrozen then st else ECDSAAdd.Divsteps.zStep st).z)
    (frozen : s.basis F.frozen=(oldFrozen || (!oldFrozen && armed && decide ((ECDSAAdd.Divsteps.zStep st).g=0))))
    (record : regValue F.offset s.basis=(if !oldFrozen && armed && decide ((ECDSAAdd.Divsteps.zStep st).g=0)
      then decoderOffset index else r)) :
    let stored := !(oldFrozen || (!oldFrozen && armed && decide ((ECDSAAdd.Divsteps.zStep st).g=0))) &&
      decide ((ECDSAAdd.Divsteps.zStep st).z≤0) && decide ((2:Int)^7∣(ECDSAAdd.Divsteps.zStep st).fv)
    run (cleanBranchProgram D.layouts p F.frozen F.work0 F.work1 (D.bank.fv.wires.getD 1 0) F.swap
      Q.history.port (List.zipWith ZeroBit.mk F.offset D.work) (decoderOffset index)) m s=
      ⟨s.phase,writeBit s.basis Q.history.port (s.basis Q.history.port ^^ (!stored && decide (ECDSAAdd.Divsteps.bbit st=1)))⟩ := by
  have geometry := compileSlotDecoder_control_geometry F Q D compiled port distinct owned budget
  have layout := compileSlotDecoder_geometry F Q D compiled distinct owned budget
  have pool := (compileSlotDecoder_pool F Q D compiled).1
  let rb := List.zipWith ZeroBit.mk F.offset D.work
  have len : rb.length=6 := by simp only [rb,List.length_zipWith,offsetWidth,pool]; decide
  have fits : decoderOffset index<2^rb.length := by rw [len]; simp only [decoderOffset]; omega
  have inputs : rb.map ZeroBit.input=F.offset := zeroViews_inputs _ _ (by rw [offsetWidth,pool]; decide)
  have bwidth : 2≤D.bank.fv.payload.length := by
    have h := layout.1.2.2.1
    simp only [WindowBank.decoderWidth] at h
    omega
  have views := D.bank.fv.asStep_views bwidth
  have notFrozen (h : s.basis F.frozen=false) : oldFrozen=false := by
    cases oldFrozen <;> simp_all
  have available := compileSlotDecoder_after_mint F Q D compiled port distinct owned budget offsetWidth index indexBound
    st s m ready one fire active sigma
    (fun h => by simpa only [notFrozen h,Bool.false_eq_true,ite_false] using rows)
    (fun h => by simpa only [notFrozen h,Bool.false_eq_true,ite_false] using counter)
  have borrow := (compileBorrowedDepths_contract _ _ _ _ _ _ _ _ _ _
    (compileSlotDecoder_contract F Q D compiled).2).1
  have bc := D.paddedArena.borrowMany_contract _ _ _ borrow
  have reserve := (D.paddedArena.reserve_success D.work.toFinset).mp ⟨D.borrowedArena,bc.2.2⟩
  have clean : ∀ b∈rb,s.basis b.work=false := by
    intro b hb
    have hw := List.mem_toFinset.mpr (decoder_zeroViews_work F.offset D.work b hb)
    exact ready b.work (reserve.1 hw) (fun hl => Finset.disjoint_left.mp reserve.2 hl hw)
  obtain ⟨a,b,c,d,e,ls,ha,hb,hc,hd,he⟩ := compileSlotDecoder_five F Q D compiled
  have ids (L : DepthLayout) (hL : L∈[a,b,c,d,e]) : L.frozen.input=F.frozen ∧ L.output=Q.history.port := by
    obtain ⟨depth,_,hdepth⟩ := compileBorrowedDepths_member _ _ _ _ _ _ _ _ _ _
      (compileSlotDecoder_contract F Q D compiled).2 L (by simpa only [ls] using hL)
    have direct := (compileBorrowedDepth_contract _ _ _ _ _ _ _ _ _ _ _ hdepth).2
    exact (compileDepth_identity _ _ _ _ _ _ _ _ _ direct).2
  have result := cleanBranchProgram_run p st inv odd a b c d e ha hb hc hd he
    F.frozen F.work0 F.work1 F.swap Q.history.port D.bank.fv.asStep rb (decoderOffset index) r
    (by rw [views.2]; exact geometry.core) geometry.compare fits oldOffset
    (by rw [views.2]; exact clearHistoryControls_away _ _ _ _ _ _ _ _ geometry.core geometry.portCompare)
    oldFrozen armed frozenZero firstZero s m clean fire active sigma frozen
    (by rw [inputs]; exact record) (by rw [views.1]; exact rows.2.2.1)
    (by intro L hL; simpa only [views.2] using available.2.2 L (by simpa only [ls] using hL))
    (fun L hL => (ids L hL).2) (fun L hL => (ids L hL).1)
  simpa only [ls,views.2] using result

end ECDSAAdd.Arithmetic.Paper935
