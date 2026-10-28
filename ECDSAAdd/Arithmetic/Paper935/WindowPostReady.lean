import ECDSAAdd.Arithmetic.Paper935.WindowPostLayout

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

theorem RoutedBankLayout.retiredWindow_post_ready (L : RoutedBankLayout) (hv : L.Valid)
    (out : WindowBank) (w : RowWindow) (A C D : Arena) (resize : Program)
    (hp : L.after.Planned out w A C resize) (z zero carry : List Wire)
    (hn : (L.active::L.q::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (hrow : (L.before.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (hown : (L.active::L.q::z).toFinset⊆A.live)
    (hbefore : List.Disjoint (L.active::L.q::z) (L.before.rows.flatMap WindowRow.wires))
    (hafter : List.Disjoint (L.active::L.q::z) (L.after.rows.flatMap WindowRow.wires))
    (hout : List.Disjoint z (out.rows.flatMap WindowRow.wires))
    (hborrow : C.reserve (zero++carry).toFinset=some D)
    (frozenWire zsign : Wire) (zlo : List Wire) (hzview : z=zlo++[zsign])
    (htag : [frozenWire,L.active,zsign,L.glow,L.parity,L.q].Nodup)
    (hparityOwn : L.parity∈A.live)
    (hprepaway : ∀ q∈L.u::L.k::(L.before.rows.flatMap WindowRow.wires++z),
      q≠L.active ∧ q≠L.parity ∧ q≠L.q)
    (hrowq : L.q∉out.rows.flatMap WindowRow.wires)
    (hsecond : out.fv.second≠L.q) (hwfv : 1≤w.fv)
    (pmod : Int) (st : ECDSAAdd.Divsteps.ZState) (hi : ECDSAAdd.Divsteps.Inv pmod st) (hpmod : pmod%2=1) (frozen : Bool) (hf : st.f%2=1)
    (s : State) (m : List Bool) (hfreeze : s.basis frozenWire=frozen)
    (hzval : signedRegValue z s.basis=st.z) (hu : s.basis L.u=false) (hk : s.basis L.k=false)
    (ha0 : s.basis L.active=false) (hq0 : s.basis L.q=false) (hb0 : s.basis L.parity=false)
    (he : L.before.Encodes s.basis st) (hzero : frozen=true → st.g=0)
    (hg : frozen=false → PayloadFits (L.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep st).g))
    (hgv : frozen=false → PayloadFits (L.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep st).gv)
    (hfv : frozen=false → PayloadFits (L.vmid.length+1) (ECDSAAdd.Divsteps.zStep st).fv)
    (hready : A.Ready s.basis) (hfit : w.Fits (if frozen then st else ECDSAAdd.Divsteps.zStep st))
    (P : WindowPostLayout) (pactive : P.active=L.active) (pfrozen : P.frozen=frozenWire)
    (persist : ∀ q∈P.one::P.frozen::P.recordWires,
      q∈A.live ∧ q∉L.before.rows.flatMap WindowRow.wires ∧ q∉z ∧
      q≠L.active ∧ q≠L.parity ∧ q≠L.q)
    (scratch : P.scratch.toFinset⊆arenaWires\C.live)
    (one : s.basis P.one=true)
    (oldOffset : P.armed=true → regValue P.recordWires s.basis<P.offset)
    (activeOffset : s.basis frozenWire=false → regValue P.recordWires s.basis=0) :
    P.Ready (run (L.retiredWindow out frozenWire zsign resize zero z carry) m s).basis := by
  let v := run (L.retiredWindow out frozenWire zsign resize zero z carry) m s
  have body := L.retiredWindow_spec hv out w A C D resize hp z zero carry hn hz hc hrow hown
    hbefore hafter hout hborrow frozenWire zsign zlo hzview htag hparityOwn hprepaway hrowq hsecond hwfv
    pmod st hi hpmod frozen hf s m hfreeze hzval hu hk ha0 hq0 hb0 he hzero hg hgv hfv hready hfit
  have keep (q : Wire) (hq : q∈P.one::P.frozen::P.recordWires) : v.basis q=s.basis q := by
    obtain ⟨a,b,c,d,e,f⟩ := persist q hq
    exact body.2.2.2.2.2.2.2.2 q a b c d e f
  have recordeq : regValue P.recordWires v.basis=regValue P.recordWires s.basis :=
    regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))
  have frozenEq : v.basis P.frozen=frozen := by rw [keep P.frozen (by simp),pfrozen,hfreeze]
  apply P.ready_of_free C v.basis body.2.1 scratch
  · exact (keep P.one (by simp)).trans one
  · rw [pactive,body.2.2.2.2.2.1,frozenEq]
  · rwa [recordeq]
  · rw [recordeq,keep P.frozen (by simp),pfrozen]
    exact activeOffset

end ECDSAAdd.Arithmetic.Paper935
