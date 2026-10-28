import ECDSAAdd.Arithmetic.Paper935.HistoryArenaReady
import ECDSAAdd.Arithmetic.Paper935.WindowControls
import ECDSAAdd.Arithmetic.Paper935.DepthControlReady

namespace ECDSAAdd.Arithmetic.Paper935

theorem storePushForget_decoder_available_clean (one zz pos sign output port : Wire) (zb : List ZeroBit)
    (frozen positive : ZeroBit) (low : List ZeroBit) (record : List Wire)
    (hnz : (output::pos::one::zz::zb.flatMap ZeroBit.wires).Nodup)
    (hnf : (one::output::(frozen::positive::low).flatMap ZeroBit.wires).Nodup)
    (hsg : sign∈zb.map ZeroBit.input) (hpos : positive.input=pos)
    (hfr : frozen.input≠pos) (hlow : ∀ b∈low,b.input≠pos)
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
      2*regValue record s.basis+(s.basis port).toNat<2^record.length) (ordinal : Nat)
    (L : DepthLayout) (valid : L.Static) (lone : L.one=one)
    (bank out : WindowBank) (A C : Arena) (padding : Program)
    (plan : bank.Planned out bank.decoderWidth A C padding)
    (pin : PinState) (tmin index : Nat) (z : List Wire)
    (ready : A.Ready s.basis) (owned : (port::record).toFinset⊆A.live)
    (rows : bank.Encodes s.basis (pinStep tmin index pin).rows)
    (counter : signedRegValue z s.basis=(pinStep tmin index pin).rows.z)
    (frozenValue : s.basis L.frozen.input=(pinStep tmin index pin).frozen)
    (historyAway : List.Disjoint (L.one::L.frozen.input::(bank.rows.flatMap WindowRow.wires++z)) (port::record))
    (retained : ∀ q∈L.one::L.frozen.input::z,q∈A.live ∧ q∉bank.rows.flatMap WindowRow.wires)
    (free : L.cleanWires.toFinset⊆arenaWires\C.live)
    (zview : L.zlo++[L.sign]=z)
    (fview : L.flow::((L.address::L.fdata)++L.ftail)=out.f.wires)
    (vview : L.vlow::(L.low.map ZeroBit.input++L.vtail)=out.fv.wires)
    (fire active second sigma : Wire) (rb : List ZeroBit) (k : Nat)
    (hn : [L.frozen.input,fire,active,second,sigma].Nodup)
    (hr : (L.frozen.input::fire::rb.flatMap ZeroBit.wires).Nodup) (hk : k<2^rb.length)
    (away : ∀ q∈L.readWires,q≠fire ∧ q≠active ∧ q≠sigma) (n tape : List Bool)
    (controlClean : ∀ q∈fire::active::sigma::rb.map ZeroBit.work,
      (run padding n (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s)).basis q=false) :
    L.Available pin.rows (run (mintHistoryControls L.frozen.input fire active second sigma rb k) tape
      (run padding n (runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s))) := by
  let t := runWithTape (storePushForget one zz pos sign output port zb frozen positive low record) m ordinal s
  have frame := storePushForget_frame_arena one zz pos sign output port zb frozen positive low record
    hnz hnf hsg hpos hfr hlow hworkpos s m hone hzz hpzero hzw hfw hpush houtzero hout hstable hfit ordinal
  have keep (q : Wire) (hq : q∈L.one::L.frozen.input::(bank.rows.flatMap WindowRow.wires++z)) :
      t.basis q=s.basis q := frame.1 q (List.disjoint_left.mp historyAway hq)
  have rows' := bank.encodes_congr s.basis t.basis _ rows
    (fun q hq => keep q (by simp only [List.mem_cons,List.mem_append]; exact Or.inr (Or.inr (Or.inl hq))))
  have counter' : signedRegValue z t.basis=(pinStep tmin index pin).rows.z := by
    unfold signedRegValue
    rw [regValue_congr z t.basis s.basis (fun q hq => keep q (by simp only [List.mem_cons,List.mem_append]; exact Or.inr (Or.inr (Or.inr hq))))]
    exact counter
  have frozen' : t.basis L.frozen.input=(pinStep tmin index pin).frozen :=
    (keep _ (by simp)).trans frozenValue
  have one' : t.basis L.one=true := (keep _ (by simp)).trans (by rw [lone]; exact hone)
  have available := L.available_after_padding valid bank out A C padding plan pin tmin index z t n
    (frame.2 A owned ready) rows' counter' frozen' one' retained free zview fview vview
  exact L.available_after_mint pin.rows L.frozen.input fire active second sigma rb k hn hr hk
    (run padding n t) tape (fun b hb => controlClean b.work (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b,hb,rfl⟩)))))
    (controlClean fire (by simp)) (controlClean active (by simp)) (controlClean sigma (by simp))
    available away

end ECDSAAdd.Arithmetic.Paper935
