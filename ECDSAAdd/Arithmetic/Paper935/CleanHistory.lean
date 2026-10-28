import ECDSAAdd.Arithmetic.Paper935.CleanBranch
import ECDSAAdd.Arithmetic.Paper935.StorePop

namespace ECDSAAdd.Arithmetic.Paper935

private theorem state_eq {a b : State} (h : a.phase=b.phase) (hb : a.basis=b.basis) : a=b := by
  cases a; cases b; simp_all

theorem storePushForget_clean_recover_pop (one zz pos sign output port : Wire) (zb : List ZeroBit)
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
    (hcontrolwork : ∀ b∈rb,(runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s).basis b.work=false)
    (hfire0 : (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s).basis fire=false)
    (hactive0 : (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s).basis active=false)
    (hsigma0 : (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s).basis sigma=false)
    (hrecord : regValue (rb.map ZeroBit.input) (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s).basis=
      (if !oldFrozen && armed && decide ((ECDSAAdd.Divsteps.zStep st).g=0) then k else r))
    (hrow : signedRegValue fv.wires (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s).basis=(if oldFrozen then st else ECDSAAdd.Divsteps.zStep st).fv)
    (hready : ∀ L∈[a,b,c,d,e],L.Available st
      (run (mintHistoryControls frozen.input fire active fv.second sigma rb k) (m.drop cursor) (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s)))
    (houts : ∀ L∈[a,b,c,d,e],L.output=port)
    (hfr : ∀ L∈[a,b,c,d,e],L.frozen.input=frozen.input)
    (vlow : Wire) (zlo tail : List Wire) (hzview : zb.map ZeroBit.input=zlo++[sign])
    (htail : tail≠[]) (hlowlen : low.length=6)
    (hzvalue : oldFrozen=false → signedRegValue (zlo++[sign]) s.basis=(ECDSAAdd.Divsteps.zStep st).z)
    (hvvalue : oldFrozen=false → signedRegValue (vlow::(low.map ZeroBit.input++tail)) s.basis=(ECDSAAdd.Divsteps.zStep st).fv)
    (hfrozen : s.basis frozen.input=(oldFrozen || (!oldFrozen && armed && decide ((ECDSAAdd.Divsteps.zStep st).g=0)))) :
    runWithTape (ECDSAAdd.Arithmetic.Divsteps.recoverBranch
        (cleanBranchProgram [a,b,c,d,e] p frozen.input fire active fv.second sigma port rb k) port
        (ordinal+measurementCount (storePush one zz pos sign output port zb frozen positive low record)) ++
      embedRecorded (storePop one zz pos sign output port zb frozen positive low record)) m cursor
      (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s)=s := by
  have hselected : (!s.basis frozen.input &&
    !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
    decide (regValue (low.map ZeroBit.input) s.basis=0))=
    (!(oldFrozen || (!oldFrozen && armed && decide ((ECDSAAdd.Divsteps.zStep st).g=0))) &&
      decide ((ECDSAAdd.Divsteps.zStep st).z≤0) && decide ((2:Int)^7 ∣ (ECDSAAdd.Divsteps.zStep st).fv)) := by
    cases ho : oldFrozen with
    | true => simp [hfrozen,ho]
    | false =>
      have hv := historyPredicate_value sign frozen.input vlow zb low zlo tail s.basis
        (ECDSAAdd.Divsteps.zStep st) hzview htail (hzvalue ho) (hvvalue ho) (hi.zStep hp).fveven
      exact hv.trans (by rw [hfrozen,hlowlen,ho])
  let selected := !s.basis frozen.input &&
    !(!s.basis sign && !decide (regValue (zb.map ZeroBit.input) s.basis=0)) &&
    decide (regValue (low.map ZeroBit.input) s.basis=0)
  let segment := storePush one zz pos sign output port zb frozen positive low record
  let t := run segment (m.drop ordinal) s
  let u := runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s
  have hs := storePush_spec one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr_1 hlow hworkpos s (m.drop ordinal) hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit
  have hu := storePushForget_run one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr_1 hlow hworkpos s m hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit ordinal
  have uzero : u.basis port=false := by rw [show u= _ from hu]; simp [writeBit]
  have phase : u.phase=(s.phase ^^ (m.getD (ordinal+measurementCount segment) false &&
      (!( !(oldFrozen || (!oldFrozen && armed && decide ((ECDSAAdd.Divsteps.zStep st).g=0))) && decide ((ECDSAAdd.Divsteps.zStep st).z≤0) &&
        decide ((2:Int)^7 ∣ (ECDSAAdd.Divsteps.zStep st).fv)) && decide (ECDSAAdd.Divsteps.bbit st=1)))) := by
    have uphase : u.phase=(s.phase ^^ (m.getD (ordinal+measurementCount segment) false && (!selected && s.basis port))) :=
      congrArg State.phase hu
    rw [uphase,← hselected,← hbranch]
  have ufr : u.basis frozen.input=s.basis frozen.input := by
    have member : frozen.input∈[one,zz,pos,sign]++zb.flatMap ZeroBit.wires++(frozen::positive::low).flatMap ZeroBit.wires := by
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨frozen,by simp,by simp [ZeroBit.wires]⟩
    have away : frozen.input∉port::record := List.disjoint_right.mp hstable member
    have hpfr : frozen.input≠port := by intro he; exact away (by simp [he])
    rw [show u= _ from hu]
    exact (Function.update_of_ne hpfr _ _).trans (hs.2.2.2.2 _ away)
  have restore := cleanBranch_cancel p st hi hp a b c d e ha hb hc hd he
    frozen.input fire active sigma port fv rb k r hn hr hk hlt hport oldFrozen armed hfg hfirst
    u m (ordinal+measurementCount segment) cursor hcontrolwork hfire0 hactive0 hsigma0
    (ufr.trans hfrozen) hrecord hrow hready houts hfr uzero s.phase phase
  have htport : t.basis port=(!selected && s.basis port) := by
    have ht := hs.2.2.1
    change t.basis port=(if selected then false else s.basis port) at ht
    cases hsel : selected <;> simpa only [hsel,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true,Bool.true_and,Bool.false_and] using ht
  have recovered : runWithTape (ECDSAAdd.Arithmetic.Divsteps.recoverBranch
      (cleanBranchProgram [a,b,c,d,e] p frozen.input fire active fv.second sigma port rb k) port
      (ordinal+measurementCount segment)) m cursor u=t := by
    rw [restore]
    apply state_eq
    · exact hs.1.symm
    · rw [← hselected,← hbranch]
      rw [show u= _ from hu]
      change writeBit (writeBit t.basis port false) port (!selected && s.basis port)=t.basis
      rw [← htport]
      simp [writeBit]
  rw [runWithTape_append,recovered,runWithTape_embedRecorded]
  exact storeHistory_roundtrip one zz pos sign output port zb frozen positive low record hnz hnf hsg hpos hfr_1 hlow hworkpos s (m.drop ordinal) hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit _

end ECDSAAdd.Arithmetic.Paper935
