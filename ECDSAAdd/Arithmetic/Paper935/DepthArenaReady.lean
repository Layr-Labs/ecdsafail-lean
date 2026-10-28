import ECDSAAdd.Arithmetic.Paper935.FrozenDepth
import ECDSAAdd.Arithmetic.Paper935.WindowBank
import ECDSAAdd.Arithmetic.Paper935.WindowSlotMath

namespace ECDSAAdd.Arithmetic.Paper935

/-- Static aliases and view lengths checked by the public layout compiler. -/
structure DepthLayout.Static (L : DepthLayout) : Prop where
  hnz : (L.flag::L.pos::L.one::L.zz::L.zb.flatMap ZeroBit.wires).Nodup
  hnf : (L.one::L.flag::(L.frozen::L.positive::L.low).flatMap ZeroBit.wires).Nodup
  hsg : L.sign∈L.zb.map ZeroBit.input
  hpos : L.positive.input=L.pos
  hfr : L.frozen.input≠L.pos
  hlow : ∀ b∈L.low,b.input≠L.pos
  hworkpos : ∀ b∈L.frozen::L.positive::L.low,b.work≠L.pos
  hnlookup : (L.flag::L.output::L.address::((L.fdata++L.qbits)++L.scratch++[L.tmp])).Nodup
  hflen : L.fdata.length=4
  hqlen : L.qbits.length=5
  hs : L.scratch.length=9
  hflag : L.flag∉[L.one,L.zz,L.pos,L.sign]++L.zb.flatMap ZeroBit.wires++(L.frozen::L.positive::L.low).flatMap ZeroBit.wires
  hout : L.output∉[L.one,L.zz,L.pos,L.sign]++L.zb.flatMap ZeroBit.wires++(L.frozen::L.positive::L.low).flatMap ZeroBit.wires
  hzview : L.zb.map ZeroBit.input=L.zlo++[L.sign]
  hvtail : L.vtail≠[]
  hmin : 2≤L.low.length
  hmax : L.low.length≤6
  hslen : L.slice.length=L.low.length
  hftail : L.ftail≠[]
  hqtail : L.qtail≠[]
  hcoeffview : L.vlow::(L.low.map ZeroBit.input++L.vtail)=L.slice++(L.qlow::(L.qbits++L.qtail))
  outputAway : L.output∉L.readWires

def DepthLayout.cleanWires (L : DepthLayout) : List Wire :=
  [L.zz,L.pos,L.flag,L.tmp]++L.zb.map ZeroBit.work++
    (L.frozen::L.positive::L.low).map ZeroBit.work++L.scratch

theorem DepthLayout.available_of_bank (L : DepthLayout) (h : L.Static)
    (A : Arena) (b : WindowBank) (z : List Wire) (st : ECDSAAdd.Divsteps.ZState)
    (s : State) (ready : A.Ready s.basis)
    (free : L.cleanWires.toFinset⊆arenaWires\A.live) (one : s.basis L.one=true)
    (zview : L.zlo++[L.sign]=z)
    (fview : L.flow::((L.address::L.fdata)++L.ftail)=b.f.wires)
    (vview : L.vlow::(L.low.map ZeroBit.input++L.vtail)=b.fv.wires)
    (rows : s.basis L.frozen.input=false → b.Encodes s.basis (ECDSAAdd.Divsteps.zStep st))
    (counter : s.basis L.frozen.input=false → signedRegValue z s.basis=(ECDSAAdd.Divsteps.zStep st).z) :
    L.Available st s := by
  have clean (q : Wire) (hq : q∈L.cleanWires) : s.basis q=false := by
    have hf := Finset.mem_sdiff.mp (free (List.mem_toFinset.mpr hq))
    exact ready q hf.1 hf.2
  have zz : s.basis L.zz=false := clean _ (by simp [cleanWires])
  have pos : s.basis L.pos=false := clean _ (by simp [cleanWires])
  have flag : s.basis L.flag=false := clean _ (by simp [cleanWires])
  have tmp : s.basis L.tmp=false := clean _ (by simp [cleanWires])
  have zw : ∀ bit∈L.zb,s.basis bit.work=false := by
    intro bit hb
    exact clean _ (by simp only [cleanWires,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨bit,hb,rfl⟩))))
  have fw : ∀ bit∈L.frozen::L.positive::L.low,s.basis bit.work=false := by
    intro bit hb
    exact clean _ (by simp only [cleanWires,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨bit,hb,rfl⟩)))
  have work : ∀ q∈L.scratch,s.basis q=false := by
    intro q hq
    exact clean _ (by simp [cleanWires,hq])
  cases frozen : s.basis L.frozen.input with
  | false =>
    apply Or.inl
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
      hzview := h.hzview
      hvtail := h.hvtail
      hmin := h.hmin
      hmax := h.hmax
      hslen := h.hslen
      hftail := h.hftail
      hqtail := h.hqtail
      hcoeffview := h.hcoeffview
      outputAway := h.outputAway
      hone := one
      hzz := zz
      hpzero := pos
      hzw := zw
      hfw := fw
      hflag0 := flag
      htmp := tmp
      hwork := work
      hzval := by rw [zview]; exact counter frozen
      hvval := by rw [vview]; exact (rows frozen).2.2.1
      hfval := by rw [fview]; exact (rows frozen).1
    }
  | true =>
    apply Or.inr
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
      hmin := h.hmin
      outputAway := h.outputAway
      hone := one
      hzz := zz
      hpzero := pos
      hzw := zw
      hfw := fw
      hflag0 := flag
      htmp := tmp
      hwork := work
      hfrozen := frozen
    }

/-- An unfrozen exit necessarily came from the active arithmetic branch. -/
theorem pinStep_unfrozen_rows (tmin index : Nat) (u : PinState)
    (h : (pinStep tmin index u).frozen=false) :
    (pinStep tmin index u).rows=ECDSAAdd.Divsteps.zStep u.rows := by
  cases hf : u.frozen with
  | true => simp [pinStep,hf] at h
  | false => simp only [pinStep_rows,hf,Bool.false_eq_true,ite_false]

theorem DepthLayout.available_of_pin (L : DepthLayout) (h : L.Static)
    (A : Arena) (b : WindowBank) (z : List Wire) (u : PinState) (tmin index : Nat)
    (s : State) (ready : A.Ready s.basis)
    (free : L.cleanWires.toFinset⊆arenaWires\A.live) (one : s.basis L.one=true)
    (zview : L.zlo++[L.sign]=z)
    (fview : L.flow::((L.address::L.fdata)++L.ftail)=b.f.wires)
    (vview : L.vlow::(L.low.map ZeroBit.input++L.vtail)=b.fv.wires)
    (rows : b.Encodes s.basis (pinStep tmin index u).rows)
    (counter : signedRegValue z s.basis=(pinStep tmin index u).rows.z)
    (frozen : s.basis L.frozen.input=(pinStep tmin index u).frozen) :
    L.Available u.rows s := by
  apply L.available_of_bank h A b z u.rows s ready free one zview fview vview
  · intro hf
    have eq := pinStep_unfrozen_rows tmin index u (frozen.symm.trans hf)
    simpa only [eq] using rows
  · intro hf
    rw [counter,pinStep_unfrozen_rows tmin index u (frozen.symm.trans hf)]

end ECDSAAdd.Arithmetic.Paper935
