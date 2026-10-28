import ECDSAAdd.Arithmetic.Paper935.WindowTagged
import ECDSAAdd.Arithmetic.Paper935.WindowSwap

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

def RoutedBankLayout.retiredWindow (L : RoutedBankLayout) (out : WindowBank)
    (frozen zsign : Wire) (resize : Program) (zero z carry : List Wire) : Program :=
  L.taggedWindow frozen zsign resize zero z carry++eraseAnd L.active out.fv.second L.q

def RoutedBankLayout.retiredWindowInverse (L : RoutedBankLayout) (out : WindowBank)
    (frozen zsign : Wire) (resize : Program) (zero z carry : List Wire) : Program :=
  [.CCX L.active out.fv.second L.q]++L.taggedWindowInverse frozen zsign resize zero z carry

theorem RoutedBankLayout.retiredWindow_roundtrip (L : RoutedBankLayout) (hv : L.Valid)
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
    (hsecond : out.fv.second≠L.q) (hwfv : 1≤w.fv)
    (pmod : Int) (st : ECDSAAdd.Divsteps.ZState) (hi : ECDSAAdd.Divsteps.Inv pmod st) (hpmod : pmod%2=1) (frozen : Bool) (hf : st.f%2=1)
    (s : State) (m n : List Bool) (hfreeze : s.basis frozenWire=frozen)
    (hzval : signedRegValue z s.basis=st.z) (hu : s.basis L.u=false) (hk : s.basis L.k=false)
    (ha0 : s.basis L.active=false) (hq0 : s.basis L.q=false) (hb0 : s.basis L.parity=false)
    (he : L.before.Encodes s.basis st) (hzero : frozen=true → st.g=0)
    (hg : frozen=false → PayloadFits (L.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep st).g))
    (hgv : frozen=false → PayloadFits (L.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep st).gv)
    (hfv : frozen=false → PayloadFits (L.vmid.length+1) (ECDSAAdd.Divsteps.zStep st).fv)
    (hready : A.Ready s.basis) (hfit : w.Fits (if frozen then st else ECDSAAdd.Divsteps.zStep st)) :
    run (L.retiredWindowInverse out frozenWire zsign resize zero z carry) n
      (run (L.retiredWindow out frozenWire zsign resize zero z carry) m s)=s := by
  let body := L.taggedWindow frozenWire zsign resize zero z carry
  let v := run body m s
  have spec := L.taggedWindow_spec hv out w A C D resize hp z zero carry hn hz hc hrow hown
    hbefore hafter hout hborrow frozenWire zsign zlo hzview htag hparityOwn hprepaway st frozen hf s m
    hfreeze hzval hu hk ha0 hq0 hb0 he hzero hg hgv hfv hready hfit
  have nonempty : out.fv.payload≠[] := by
    intro hnil
    have width := spec.2.2.2.1.2.2.1
    rw [hnil] at width
    simp only [List.length_nil] at width
    omega
  have aq : L.active≠L.q := fun heq => (List.nodup_cons.mp hn).1 (by simp [heq])
  have ret := out.fv.retire_swap nonempty pmod st hi hpmod frozen L.active L.q v
    (m.drop (measurementCount body)) n aq hsecond spec.2.2.2.2.2.1 spec.2.2.2.2.2.2.1
    spec.2.2.1.2.2.1 hzero
  rw [retiredWindow,run_append,run_take,retiredWindowInverse,run_append,run_take,ret.2]
  exact L.taggedWindow_roundtrip hv out w A C D resize hp z zero carry hn hz hc hrow hown
    hbefore hafter hborrow frozenWire zsign zlo hzview htag hparityOwn hprepaway st frozen hf s m _
    hfreeze hzval hu hk ha0 hq0 hb0 he hzero hg hgv hfv hready hfit

theorem RoutedBankLayout.retiredWindow_spec (L : RoutedBankLayout) (hv : L.Valid)
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
    (hready : A.Ready s.basis) (hfit : w.Fits (if frozen then st else ECDSAAdd.Divsteps.zStep st)) :
    let t := run (L.retiredWindow out frozenWire zsign resize zero z carry) m s
    t.phase=s.phase ∧ C.Ready t.basis ∧
    out.Encodes t.basis (if frozen then st else ECDSAAdd.Divsteps.zStep st) ∧ out.Widths w ∧
    regValue z t.basis=counterWord z.length (!frozen) (decide (0≤st.z ∧ st.g%2=1)) (regValue z s.basis) ∧
    t.basis L.active= !frozen ∧ t.basis L.q=false ∧
    t.basis L.parity=decide (ECDSAAdd.Divsteps.bbit st=1) ∧
    (∀ q∈A.live,q∉L.before.rows.flatMap WindowRow.wires → q∉z →
      q≠L.active → q≠L.parity → q≠L.q → t.basis q=s.basis q) := by
  let body := L.taggedWindow frozenWire zsign resize zero z carry
  let v := run body m s
  have spec := L.taggedWindow_spec hv out w A C D resize hp z zero carry hn hz hc hrow hown
    hbefore hafter hout hborrow frozenWire zsign zlo hzview htag hparityOwn hprepaway st frozen hf s m
    hfreeze hzval hu hk ha0 hq0 hb0 he hzero hg hgv hfv hready hfit
  have nonempty : out.fv.payload≠[] := by
    intro hnil
    have width := spec.2.2.2.1.2.2.1
    rw [hnil] at width
    simp only [List.length_nil] at width
    omega
  have aq : L.active≠L.q := fun heq => (List.nodup_cons.mp hn).1 (by simp [heq])
  have ret := out.fv.retire_swap nonempty pmod st hi hpmod frozen L.active L.q v
    (m.drop (measurementCount body)) [] aq hsecond spec.2.2.2.2.2.1 spec.2.2.2.2.2.2.1
    spec.2.2.1.2.2.1 hzero
  have qz : L.q∉z := by
    have h := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
    intro hh; exact h (by simp [hh])
  have pq : L.parity≠L.q := by simp_all
  dsimp only
  rw [retiredWindow,run_append,run_take,ret.1]
  refine ⟨spec.1,?_,?_,spec.2.2.2.1,?_,?_,by simp [writeBit],?_,?_⟩
  · intro q hq hn
    by_cases eq : q=L.q
    · subst q; simp [writeBit]
    · simpa [writeBit,eq] using spec.2.1 q hq hn
  · apply out.encodes_congr v.basis _ _ spec.2.2.1
    intro q hq
    simp [writeBit,show q≠L.q from fun eq => hrowq (eq ▸ hq)]
  · rw [regValue_congr z (writeBit v.basis L.q false) v.basis (fun q hq => by
      simp [writeBit,show q≠L.q from fun eq => qz (eq ▸ hq)])]
    exact spec.2.2.2.2.1
  · simpa [writeBit,aq] using spec.2.2.2.2.2.1
  · simpa [writeBit,pq] using spec.2.2.2.2.2.2.2.1
  · intro q hq hr hz qa qp qq
    simpa [writeBit,qq] using spec.2.2.2.2.2.2.2.2 q hq hr hz qa qp qq

end ECDSAAdd.Arithmetic.Paper935
