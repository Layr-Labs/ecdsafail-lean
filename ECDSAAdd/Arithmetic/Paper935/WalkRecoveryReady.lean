import ECDSAAdd.Arithmetic.Paper935.WalkRecovery

namespace ECDSAAdd.Arithmetic.Paper935

/-- Build the local history certificate from the concrete padded five-depth
recovery theorem. All original layout, encoding, cleanliness, finite-stack and
saved-record conditions remain explicit; no inverse correctness is postulated. -/
theorem historyUndoAt_of_ready (one zz pos sign output port : Wire) (zb : List ZeroBit)
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
    (controlFree : (fire::active::sigma::rb.map ZeroBit.work).toFinset⊆arenaWires\C.live)
    (away : ∀ L∈[a,b,c,d,e],∀ q∈L.readWires,q≠fire ∧ q≠active ∧ q≠sigma) :
    HistoryUndoAt ⟨one,zz,pos,sign,output,port,zb,frozen,positive,low,record⟩
      (paddedCleanBranch padding [a,b,c,d,e] p frozen.input fire active fv.second sigma port rb k)
      m ordinal cursor s := by
  exact storePushForget_ready_recover_pop
    one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr_1 hlow hworkpos s m hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit ordinal cursor padding proper padport padfrozen p st hi hp a b c d e ha hb hc hd he sigma fire active fv rb k r hn hr hk hlt hport oldFrozen armed hfg hfirst hbranch hcontrolwork hfire0 hactive0 hsigma0 hrecord hrow houts hfr vlow zlo tail hzview htail hlowlen hzvalue hvvalue hfrozen bank paddedBank A C plan tmin index z arenaReady historyOwned rows counter pinFrozen statics ones historyAway retained free zviews fviews vviews controlFree away

/-- The arithmetic part of a local certificate is supplied by the actual
compiled public-slot roundtrip theorem, with an arbitrary reverse tape. -/
theorem slotUndoConditions_of_compiled (A : Arena) (b : WindowBank) (addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (probeWidth tmin index : Nat) (Q : HistoricalSlot)
    (h : compileCheckedPublicSlot A b addWidth exitWidth F (decide (tmin≤ index)) probeWidth (index+1-tmin)=some Q.slot)
    (checks : Q.slot.front.MathChecks F exitWidth)
    (old : PinState) (s : State) (m : List Bool) (ordinal cursor : Nat) (decoder : Program) (ready : A.Ready s.basis)
    (rows : b.Encodes s.basis old.rows) (prefit : addWidth.Fits old.rows)
    (values : F.Values s.basis old) (owned : F.wires.toFinset⊆A.live)
    (away : List.Disjoint F.wires (b.rows.flatMap WindowRow.wires))
    (p : Int) (inv : ECDSAAdd.Divsteps.Inv p old.rows) (odd : p%2=1) (fodd : old.rows.f%2=1)
    (frozenZero : old.frozen=true → old.rows.g=0)
    (gfit : old.frozen=false → PayloadFits (Q.slot.front.layout.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep old.rows).g))
    (gvfit : old.frozen=false → PayloadFits (Q.slot.front.layout.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep old.rows).gv)
    (fvfit : old.frozen=false → PayloadFits (Q.slot.front.layout.vmid.length+1) (ECDSAAdd.Divsteps.zStep old.rows).fv)
    (exitfit : exitWidth.Fits (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows))
    (zfit : PayloadFits (F.counter.length-1) (if old.frozen then old.rows else ECDSAAdd.Divsteps.zStep old.rows).z)
    (oldOffset : tmin≤ index → old.offset< index+1-tmin) (activeOffset : old.frozen=false → old.offset=0)

    (history : HistoryUndoAt Q.history decoder m (ordinal+measurementCount (Q.slot.program F)) cursor
      (run (Q.slot.program F) (m.drop ordinal) s)) :
    SlotUndoConditions Q F decoder m ordinal cursor s := by
  refine ⟨?_,history⟩
  intro n
  exact compileCheckedPublicSlot_roundtrip
    A b addWidth exitWidth F probeWidth tmin index Q.slot h checks old s (m.drop ordinal) n ready rows prefit values owned away p inv odd fodd frozenZero gfit gvfit fvfit exitfit zfit oldOffset activeOffset

end ECDSAAdd.Arithmetic.Paper935
