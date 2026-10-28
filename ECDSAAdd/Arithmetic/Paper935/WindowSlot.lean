import ECDSAAdd.Arithmetic.Paper935.WindowPostReady

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

/-- A real windowed slot through blocked freeze/offset post-processing. The
branch parity is retained here for the separately proved history transport. -/
def RoutedBankLayout.windowSlot (L : RoutedBankLayout) (out : WindowBank) (P : WindowPostLayout)
    (frozen zsign : Wire) (resize : Program) (zero z carry : List Wire) : Program :=
  L.retiredWindow out frozen zsign resize zero z carry++P.program

def RoutedBankLayout.windowSlotInverse (L : RoutedBankLayout) (out : WindowBank) (P : WindowPostLayout)
    (frozen zsign : Wire) (resize : Program) (zero z carry : List Wire) : Program :=
  P.inverse++L.retiredWindowInverse out frozen zsign resize zero z carry

theorem RoutedBankLayout.windowSlot_roundtrip (L : RoutedBankLayout) (hv : L.Valid)
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
    (s : State) (m n : List Bool) (hfreeze : s.basis frozenWire=frozen)
    (hzval : signedRegValue z s.basis=st.z) (hu : s.basis L.u=false) (hk : s.basis L.k=false)
    (ha0 : s.basis L.active=false) (hq0 : s.basis L.q=false) (hb0 : s.basis L.parity=false)
    (he : L.before.Encodes s.basis st) (hzero : frozen=true → st.g=0)
    (hg : frozen=false → PayloadFits (L.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep st).g))
    (hgv : frozen=false → PayloadFits (L.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep st).gv)
    (hfv : frozen=false → PayloadFits (L.vmid.length+1) (ECDSAAdd.Divsteps.zStep st).fv)
    (hready : A.Ready s.basis) (hfit : w.Fits (if frozen then st else ECDSAAdd.Divsteps.zStep st))
    (P : WindowPostLayout) (pvalid : P.Valid) (pactive : P.active=L.active) (pfrozen : P.frozen=frozenWire)
    (persist : ∀ q∈P.one::P.frozen::P.recordWires,
      q∈A.live ∧ q∉L.before.rows.flatMap WindowRow.wires ∧ q∉z ∧
      q≠L.active ∧ q≠L.parity ∧ q≠L.q)
    (scratch : P.scratch.toFinset⊆arenaWires\C.live)
    (one : s.basis P.one=true)
    (oldOffset : P.armed=true → regValue P.recordWires s.basis<P.offset)
    (activeOffset : s.basis frozenWire=false → regValue P.recordWires s.basis=0) :
    run (L.windowSlotInverse out P frozenWire zsign resize zero z carry) n
      (run (L.windowSlot out P frozenWire zsign resize zero z carry) m s)=s := by
  have ready := L.retiredWindow_post_ready hv out w A C D resize hp z zero carry hn hz hc hrow hown
    hbefore hafter hout hborrow frozenWire zsign zlo hzview htag hparityOwn hprepaway hrowq hsecond hwfv
    pmod st hi hpmod frozen hf s m hfreeze hzval hu hk ha0 hq0 hb0 he hzero hg hgv hfv hready hfit
    P pactive pfrozen persist scratch one oldOffset activeOffset
  rw [windowSlot,run_append,run_take,windowSlotInverse,run_append,run_take,P.roundtrip pvalid _ _ n ready]
  exact L.retiredWindow_roundtrip hv out w A C D resize hp z zero carry hn hz hc hrow hown
    hbefore hafter hout hborrow frozenWire zsign zlo hzview htag hparityOwn hprepaway hsecond hwfv
    pmod st hi hpmod frozen hf s m _ hfreeze hzval hu hk ha0 hq0 hb0 he hzero hg hgv hfv hready hfit

end ECDSAAdd.Arithmetic.Paper935
