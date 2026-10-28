import ECDSAAdd.Arithmetic.Paper935.DecoderBankReady
import ECDSAAdd.Arithmetic.Paper935.HistoryControls

namespace ECDSAAdd.Arithmetic.Paper935

theorem DepthLayout.Ready.frame_read (L : DepthLayout) (st : ECDSAAdd.Divsteps.ZState)
    (s t : State) (h : L.Ready st s)
    (hframe : ∀ w∈L.readWires,t.basis w=s.basis w) : L.Ready st t := by
  have keep (w : Wire) (hw : w∈L.readWires) : t.basis w=s.basis w :=
    hframe w hw
  have root (w : Wire) (hw : w∈[L.one,L.zz,L.pos,L.sign,L.flag,L.tmp]) : w∈L.readWires := by
    simp only [DepthLayout.readWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto
  have inZ (w : Wire) (hw : w∈L.zb.flatMap ZeroBit.wires) : w∈L.readWires := by
    simp only [DepthLayout.readWires,List.mem_append]
    tauto
  have inF (w : Wire) (hw : w∈(L.frozen::L.positive::L.low).flatMap ZeroBit.wires) : w∈L.readWires := by
    simp only [DepthLayout.readWires,List.mem_append]
    tauto
  have inScratch (w : Wire) (hw : w∈L.scratch) : w∈L.readWires := by
    simp only [DepthLayout.readWires,List.mem_append]
    tauto
  have signed (xs : List Wire) (hx : xs⊆L.readWires) : signedRegValue xs t.basis=signedRegValue xs s.basis := by
    unfold signedRegValue
    rw [regValue_congr xs t.basis s.basis (fun w hw => keep w (hx hw))]
  have zkeep : signedRegValue (L.zlo++[L.sign]) t.basis=signedRegValue (L.zlo++[L.sign]) s.basis := by
    apply signed
    intro w hw
    simp only [DepthLayout.readWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto
  have vkeep : signedRegValue (L.vlow::(L.low.map ZeroBit.input++L.vtail)) t.basis=
      signedRegValue (L.vlow::(L.low.map ZeroBit.input++L.vtail)) s.basis := by
    apply signed
    intro w hw
    simp only [DepthLayout.readWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto
  have fkeep : signedRegValue (L.flow::((L.address::L.fdata)++L.ftail)) t.basis=
      signedRegValue (L.flow::((L.address::L.fdata)++L.ftail)) s.basis := by
    apply signed
    intro w hw
    simp only [DepthLayout.readWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto
  have zw : ∀ b∈L.zb,t.basis b.work=false := by
    intro b hb
    exact (keep b.work (inZ _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))).trans (h.hzw b hb)
  have fw : ∀ b∈L.frozen::L.positive::L.low,t.basis b.work=false := by
    intro b hb
    exact (keep b.work (inF _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))).trans (h.hfw b hb)
  exact {
    hnz := h.hnz
    hnf := h.hnf
    hsg := h.hsg
    hpos := h.hpos
    hfr := h.hfr
    hlow := h.hlow
    hworkpos := h.hworkpos
    hnlookup := h.hnlookup
    hflen := h.hflen
    hqlen := h.hqlen
    hs := h.hs
    hflag := h.hflag
    hout := h.hout
    hone := (keep L.one (root _ (by simp))).trans h.hone
    hzz := (keep L.zz (root _ (by simp))).trans h.hzz
    hpzero := (keep L.pos (root _ (by simp))).trans h.hpzero
    hzw := zw
    hfw := fw
    hflag0 := (keep L.flag (root _ (by simp))).trans h.hflag0
    htmp := (keep L.tmp (root _ (by simp))).trans h.htmp
    hwork := fun w hw => (keep w (inScratch w hw)).trans (h.hwork w hw)
    hzview := h.hzview
    hvtail := h.hvtail
    hmin := h.hmin
    hmax := h.hmax
    hslen := h.hslen
    hftail := h.hftail
    hqtail := h.hqtail
    hzval := zkeep.trans h.hzval
    hvval := vkeep.trans h.hvval
    hfval := fkeep.trans h.hfval
    hcoeffview := h.hcoeffview
    outputAway := h.outputAway
  }


private theorem state_eq {a b : State} (h : a.phase=b.phase) (hb : a.basis=b.basis) : a=b := by
  cases a; cases b; simp_all

theorem DepthLayout.FrozenReady.frame_read (L : DepthLayout)
    (s t : State) (h : L.FrozenReady s)
    (hframe : ∀ w∈L.readWires,t.basis w=s.basis w) : L.FrozenReady t := by
  have keep (w : Wire) (hw : w∈L.readWires) : t.basis w=s.basis w :=
    hframe w hw
  have root (w : Wire) (hw : w∈[L.one,L.zz,L.pos,L.sign,L.flag,L.tmp]) : w∈L.readWires := by
    simp only [DepthLayout.readWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
    tauto
  have inZ (w : Wire) (hw : w∈L.zb.flatMap ZeroBit.wires) : w∈L.readWires := by
    simp only [DepthLayout.readWires,List.mem_append]
    tauto
  have inF (w : Wire) (hw : w∈(L.frozen::L.positive::L.low).flatMap ZeroBit.wires) : w∈L.readWires := by
    simp only [DepthLayout.readWires,List.mem_append]
    tauto
  have inScratch (w : Wire) (hw : w∈L.scratch) : w∈L.readWires := by
    simp only [DepthLayout.readWires,List.mem_append]
    tauto
  have zw : ∀ b∈L.zb,t.basis b.work=false := by
    intro b hb
    exact (keep b.work (inZ _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))).trans (h.hzw b hb)
  have fw : ∀ b∈L.frozen::L.positive::L.low,t.basis b.work=false := by
    intro b hb
    exact (keep b.work (inF _ (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩))).trans (h.hfw b hb)
  exact {
    hnz := h.hnz
    hnf := h.hnf
    hsg := h.hsg
    hpos := h.hpos
    hfr := h.hfr
    hlow := h.hlow
    hworkpos := h.hworkpos
    hnlookup := h.hnlookup
    hflen := h.hflen
    hqlen := h.hqlen
    hs := h.hs
    hflag := h.hflag
    hout := h.hout
    hone := (keep L.one (root _ (by simp))).trans h.hone
    hzz := (keep L.zz (root _ (by simp))).trans h.hzz
    hpzero := (keep L.pos (root _ (by simp))).trans h.hpzero
    hzw := zw
    hfw := fw
    hflag0 := (keep L.flag (root _ (by simp))).trans h.hflag0
    htmp := (keep L.tmp (root _ (by simp))).trans h.htmp
    hwork := fun w hw => (keep w (inScratch w hw)).trans (h.hwork w hw)
    hmin := h.hmin
    hfrozen := (keep L.frozen.input L.frozen_mem).trans h.hfrozen
    outputAway := h.outputAway
  }

theorem DepthLayout.Available.frame_read (L : DepthLayout) (st : ECDSAAdd.Divsteps.ZState)
    (s t : State) (h : L.Available st s)
    (keep : ∀ q∈L.readWires,t.basis q=s.basis q) : L.Available st t := by
  rcases h with h|h
  · exact Or.inl (DepthLayout.Ready.frame_read L st s t h keep)
  · exact Or.inr (DepthLayout.FrozenReady.frame_read L s t h keep)

theorem DepthLayout.available_after_mint (L : DepthLayout) (st : ECDSAAdd.Divsteps.ZState)
    (frozen fire active second sigma : Wire) (rb : List ZeroBit) (k : Nat)
    (hn : [frozen,fire,active,second,sigma].Nodup)
    (hr : (frozen::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length)
    (s : State) (m : List Bool) (hc : ∀ b∈rb,s.basis b.work=false)
    (hfire : s.basis fire=false) (ha : s.basis active=false) (hq : s.basis sigma=false)
    (ready : L.Available st s)
    (away : ∀ q∈L.readWires,q≠fire ∧ q≠active ∧ q≠sigma) :
    L.Available st (ECDSAAdd.run (mintHistoryControls frozen fire active second sigma rb k) m s) := by
  apply DepthLayout.Available.frame_read L st s _ ready
  intro q hq'
  obtain ⟨a,b,c⟩ := away q hq'
  rw [mintHistoryControls_run frozen fire active second sigma rb k hn hr hk s m hc hfire ha hq]
  simp only [writeBit,Function.update_of_ne a,Function.update_of_ne b,Function.update_of_ne c]

theorem DepthLayout.available_after_padding_mint (L : DepthLayout) (valid : L.Static)
    (b out : WindowBank) (A C : Arena) (padding : Program)
    (plan : b.Planned out b.decoderWidth A C padding)
    (u : PinState) (tmin index : Nat) (z : List Wire) (s : State) (m : List Bool)
    (ready : A.Ready s.basis) (rows : b.Encodes s.basis (pinStep tmin index u).rows)
    (counter : signedRegValue z s.basis=(pinStep tmin index u).rows.z)
    (frozen : s.basis L.frozen.input=(pinStep tmin index u).frozen)
    (one : s.basis L.one=true)
    (retained : ∀ q∈L.one::L.frozen.input::z,q∈A.live ∧ q∉b.rows.flatMap WindowRow.wires)
    (free : L.cleanWires.toFinset⊆arenaWires\C.live)
    (zview : L.zlo++[L.sign]=z)
    (fview : L.flow::((L.address::L.fdata)++L.ftail)=out.f.wires)
    (vview : L.vlow::(L.low.map ZeroBit.input++L.vtail)=out.fv.wires)
    (fire active second sigma : Wire) (rb : List ZeroBit) (k : Nat)
    (hn : [L.frozen.input,fire,active,second,sigma].Nodup)
    (hr : (L.frozen.input::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length)
    (controlFree : (fire::active::sigma::rb.map ZeroBit.work).toFinset⊆arenaWires\C.live)
    (away : ∀ q∈L.readWires,q≠fire ∧ q≠active ∧ q≠sigma) (n : List Bool) :
    L.Available u.rows (ECDSAAdd.run (mintHistoryControls L.frozen.input fire active second sigma rb k)
      n (ECDSAAdd.run padding m s)) := by
  have available := L.available_after_padding valid b out A C padding plan u tmin index z s m
    ready rows counter frozen one retained free zview fview vview
  have result := b.resize_correct out b.decoderWidth A C padding plan s m _ ready rows
    (b.decoderWidth_fits s.basis _ rows)
  have clean (q : Wire) (hq : q∈fire::active::sigma::rb.map ZeroBit.work) :
      (ECDSAAdd.run padding m s).basis q=false := by
    have hh := Finset.mem_sdiff.mp (controlFree (List.mem_toFinset.mpr hq))
    exact result.2.1 q hh.1 hh.2
  apply L.available_after_mint u.rows L.frozen.input fire active second sigma rb k hn hr hk
    (ECDSAAdd.run padding m s) n
    (fun bit hb => clean bit.work (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨bit,hb,rfl⟩)))))
    (clean fire (by simp)) (clean active (by simp)) (clean sigma (by simp)) available away

end ECDSAAdd.Arithmetic.Paper935
