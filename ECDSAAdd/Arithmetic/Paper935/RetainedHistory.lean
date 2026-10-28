import ECDSAAdd.Arithmetic.Paper935.HistoryDecoderRetained
import ECDSAAdd.Arithmetic.Paper935.PaddedHistory

namespace ECDSAAdd.Arithmetic.Paper935

theorem storePushForget_retained_recover_pop (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire)
    (hnz : (output::pos::one::zz::zb.flatMap ZeroBit.wires).Nodup)
    (hnf : (one::output::(frozen::positive::low).flatMap ZeroBit.wires).Nodup)
    (hsg : sign∈zb.map ZeroBit.input) (hpos : positive.input=pos)
    (hfr_1 : frozen.input≠pos) (hlow : ∀ b∈low,b.input≠pos)
    (hworkpos : ∀ b∈frozen::positive::low,b.work≠pos)
    (s : State) (m : List Bool) (hone : s.basis one=true)
    (hzz : s.basis zz=false) (hpzero : s.basis pos=false)
    (hzw : ∀ b∈zb,s.basis b.work=false)
    (hfw : ∀ b∈frozen::positive::low,s.basis b.work=false)
    (hpush : (output::port::record).Nodup) (houtzero : s.basis output=false)
    (hout : output∉[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires)
    (hstable : List.Disjoint (port::record)
      ([one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires))
    (hfit : (!s.basis frozen.input &&
      !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
      decide (regValue (low.map ZeroBit.input) s.basis=0))=true →
      2*regValue record s.basis+(s.basis port).toNat<2^record.length) (ordinal cursor : Nat)
    (padding : Program) (proper : ProperProgram padding) (padport : port∉wires padding)
    (padfrozen : frozen.input∉wires padding)
    (p : Int) (st : ECDSAAdd.Divsteps.ZState) (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1)
    (a b c d e : DepthLayout) (ha : a.low.length=2) (hb : b.low.length=3)
    (hc : c.low.length=4) (hd : d.low.length=5) (he : e.low.length=6)
    (sigma fire active : Wire) (fv : ECDSAAdd.Arithmetic.Divsteps.StepRow) (rb : List ZeroBit) (k r : Nat)
    (hn : [frozen.input,fire,active,fv.second,sigma,port].Nodup)
    (hr : (frozen.input::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length) (hlt : r<k)
    (hport : port∉wires (clearHistoryControls frozen.input fire active fv.second sigma rb k))
    (oldFrozen armed : Bool) (hfg : oldFrozen=true → st.g=0)
    (hfirst : oldFrozen=false → armed=true → (ECDSAAdd.Divsteps.zStep st).g=0 → st.g≠0)
    (hbranch : s.basis port=decide (ECDSAAdd.Divsteps.bbit st=1))
    (hcontrolwork : ∀ b∈rb,(run padding (m.drop cursor) (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s)).basis b.work=false)
    (hfire0 : (run padding (m.drop cursor) (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s)).basis fire=false)
    (hactive0 : (run padding (m.drop cursor) (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s)).basis active=false)
    (hsigma0 : (run padding (m.drop cursor) (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s)).basis sigma=false)
    (hrecord : regValue (rb.map ZeroBit.input) (run padding (m.drop cursor) (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s)).basis=
      (if !oldFrozen && armed && decide ((ECDSAAdd.Divsteps.zStep st).g=0) then k else r))
    (hrow : signedRegValue fv.wires (run padding (m.drop cursor) (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s)).basis=(if oldFrozen then st else ECDSAAdd.Divsteps.zStep st).fv)
    (houts : ∀ L∈[a,b,c,d,e],L.output=port)
    (hfr : ∀ L∈[a,b,c,d,e],L.frozen.input=frozen.input)
    (vlow : Wire) (zlo tail : List Wire) (hzview : zb.map ZeroBit.input=zlo++[sign])
    (htail : tail≠[]) (hlowlen : low.length=6)
    (hzvalue : oldFrozen=false → signedRegValue (zlo++[sign]) s.basis=(ECDSAAdd.Divsteps.zStep st).z)
    (hvvalue : oldFrozen=false → signedRegValue (vlow::(low.map ZeroBit.input++tail)) s.basis=(ECDSAAdd.Divsteps.zStep st).fv)
    (hfrozen : s.basis frozen.input=(oldFrozen || (!oldFrozen && armed && decide ((ECDSAAdd.Divsteps.zStep st).g=0))))
    (bank paddedBank : WindowBank) (A C : Arena)
    (plan : bank.Planned paddedBank bank.decoderWidth A C padding)
    (tmin index : Nat) (z : List Wire)
    (arenaReady : A.Ready s.basis) (historyOwned : (port::record).toFinset⊆A.live)
    (rows : bank.Encodes s.basis (pinStep tmin index ⟨st,oldFrozen,r⟩).rows)
    (counter : signedRegValue z s.basis=(pinStep tmin index ⟨st,oldFrozen,r⟩).rows.z)
    (pinFrozen : s.basis frozen.input=(pinStep tmin index ⟨st,oldFrozen,r⟩).frozen)
    (statics : ∀ L∈[a,b,c,d,e],L.Static)
    (ones : ∀ L∈[a,b,c,d,e],L.one=one)
    (historyAway : ∀ L∈[a,b,c,d,e],List.Disjoint
      (L.one::L.frozen.input::(bank.rows.flatMap WindowRow.wires++z)) (port::record))
    (retained : ∀ L∈[a,b,c,d,e],∀ q∈L.one::L.frozen.input::z,
      q∈A.live ∧ q∉bank.rows.flatMap WindowRow.wires)
    (free : ∀ L∈[a,b,c,d,e],L.cleanWires.toFinset⊆arenaWires\C.live)
    (zviews : ∀ L∈[a,b,c,d,e],L.zlo++[L.sign]=z)
    (fviews : ∀ L∈[a,b,c,d,e],L.flow::((L.address::L.fdata)++L.ftail)=paddedBank.f.wires)
    (vviews : ∀ L∈[a,b,c,d,e],L.vlow::(L.low.map ZeroBit.input++L.vtail)=paddedBank.fv.wires)
    (away : ∀ L∈[a,b,c,d,e],∀ q∈L.readWires,q≠fire ∧ q≠active ∧ q≠sigma) :
    runWithTape (ECDSAAdd.Arithmetic.Divsteps.recoverBranch
        (paddedCleanBranch padding [a,b,c,d,e] p frozen.input fire active fv.second sigma port rb k) port
        (ordinal+measurementCount (storePush one zz pos sign output port zb frozen positive low record)) ++
      embedRecorded (storePop one zz pos sign output port zb frozen positive low record)) m cursor
      (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s)=s := by
  apply storePushForget_padded_recover_pop one zz pos sign output port zb frozen positive low record
    hnz hnf hsg hpos hfr_1 hlow hworkpos s m hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit
    ordinal cursor padding proper padport padfrozen p st hi hp a b c d e ha hb hc hd he
    sigma fire active fv rb k r hn hr hk hlt hport oldFrozen armed hfg hfirst hbranch
    hcontrolwork hfire0 hactive0 hsigma0 hrecord hrow _ houts hfr vlow zlo tail hzview htail hlowlen
    hzvalue hvvalue hfrozen
  intro L hL
  have hnc : [frozen.input,fire,active,fv.second,sigma].Nodup :=
    List.Nodup.of_append_left (l₂ := [port]) (by simpa only [List.cons_append,List.nil_append] using hn)
  have result := storePushForget_decoder_available_clean one zz pos sign output port zb frozen positive low record
    hnz hnf hsg hpos hfr_1 hlow hworkpos s m hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit ordinal
    L (statics L hL) (ones L hL) bank paddedBank A C padding plan ⟨st,oldFrozen,r⟩ tmin index z
    arenaReady historyOwned rows counter (by rw [hfr L hL]; exact pinFrozen)
    (historyAway L hL) (retained L hL) (free L hL) (zviews L hL) (fviews L hL) (vviews L hL)
    fire active fv.second sigma rb k (by rw [hfr L hL]; exact hnc) (by rw [hfr L hL]; exact hr)
    hk (away L hL) (m.drop cursor) (m.drop cursor) (by
      intro q hq
      simp only [List.mem_cons,List.mem_map] at hq
      rcases hq with rfl | rfl | rfl | ⟨b,hb,rfl⟩
      · exact hfire0
      · exact hactive0
      · exact hsigma0
      · exact hcontrolwork b hb)
  simpa only [hfr L hL] using result

end ECDSAAdd.Arithmetic.Paper935
