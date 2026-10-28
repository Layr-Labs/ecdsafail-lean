import ECDSAAdd.Arithmetic.Paper935.WindowControls
import ECDSAAdd.Arithmetic.Paper935.WindowStepFrame

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

def RoutedBankLayout.taggedWindow (L : RoutedBankLayout) (frozen zsign : Wire)
    (resize : Program) (zero z carry : List Wire) : Program :=
  L.mintControls frozen zsign++L.windowStep resize zero z carry

def RoutedBankLayout.taggedWindowInverse (L : RoutedBankLayout) (frozen zsign : Wire)
    (resize : Program) (zero z carry : List Wire) : Program :=
  L.windowStepInverse resize zero z carry++(L.mintControls frozen zsign).reverse

theorem RoutedBankLayout.taggedWindow_roundtrip (L : RoutedBankLayout) (hv : L.Valid)
    (out : WindowBank) (w : RowWindow) (A C D : Arena) (resize : Program)
    (hp : L.after.Planned out w A C resize) (z zero carry : List Wire)
    (hn : (L.active::L.q::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (hrow : (L.before.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (hown : (L.active::L.q::z).toFinset⊆A.live)
    (hbefore : List.Disjoint (L.active::L.q::z) (L.before.rows.flatMap WindowRow.wires))
    (hafter : List.Disjoint (L.active::L.q::z) (L.after.rows.flatMap WindowRow.wires))
    (hborrow : C.reserve (zero++carry).toFinset=some D)
    (frozenWire zsign : Wire) (zlo : List Wire) (hzview : z=zlo++[zsign])
    (htag : [frozenWire,L.active,zsign,L.glow,L.parity,L.q].Nodup)
    (hparityOwn : L.parity∈A.live)
    (hprepaway : ∀ q∈L.u::L.k::(L.before.rows.flatMap WindowRow.wires++z),
      q≠L.active ∧ q≠L.parity ∧ q≠L.q)
    (st : ECDSAAdd.Divsteps.ZState) (frozen : Bool) (hf : st.f%2=1)
    (s : State) (m n : List Bool) (hfreeze : s.basis frozenWire=frozen)
    (hzval : signedRegValue z s.basis=st.z) (hu : s.basis L.u=false) (hk : s.basis L.k=false)
    (ha0 : s.basis L.active=false) (hq0 : s.basis L.q=false) (hb0 : s.basis L.parity=false)
    (he : L.before.Encodes s.basis st) (hzero : frozen=true → st.g=0)
    (hg : frozen=false → PayloadFits (L.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep st).g))
    (hgv : frozen=false → PayloadFits (L.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep st).gv)
    (hfv : frozen=false → PayloadFits (L.vmid.length+1) (ECDSAAdd.Divsteps.zStep st).fv)
    (hready : A.Ready s.basis) (hfit : w.Fits (if frozen then st else ECDSAAdd.Divsteps.zStep st)) :
    run (L.taggedWindowInverse frozenWire zsign resize zero z carry) n
      (run (L.taggedWindow frozenWire zsign resize zero z carry) m s)=s := by
  have tagvalid : [zsign,L.glow,L.parity,L.q].Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp htag).2).2
  have fa : frozenWire≠L.active := by simp_all
  have activeSep : L.active∉[zsign,L.glow,L.parity,L.q] :=
    (List.nodup_cons.mp (List.nodup_cons.mp htag).2).1
  let v := run (L.mintControls frozenWire zsign) m s
  have prep := L.mintControls_run frozenWire zsign tagvalid fa activeSep st zlo s m ha0 hb0 hq0
    (by simpa only [←hzview] using hzval) he.2.1
  have keep (q : Wire) (hq : q∈L.u::L.k::(L.before.rows.flatMap WindowRow.wires++z)) :
      v.basis q=s.basis q := by
    obtain ⟨a,b,c⟩ := hprepaway q hq
    exact prep.2.2.2.2 q a b c
  have ve : L.before.Encodes v.basis st := L.before.encodes_congr s.basis v.basis st he
    (fun q hq => keep q (by simp [hq]))
  have va : v.basis L.active= !frozen := prep.2.1.trans (congrArg Bool.not hfreeze)
  have vq : v.basis L.q=decide (0≤st.z ∧ st.g%2=1) := prep.2.2.2.1
  have vb : v.basis L.parity=decide (ECDSAAdd.Divsteps.bbit st=1) := by
    rw [prep.2.2.1]
    unfold ECDSAAdd.Divsteps.parityControl ECDSAAdd.Divsteps.bbit
    split_ifs <;> simp_all
  have ready : A.Ready v.basis := by
    intro q hq hn
    have qa : q≠L.active := fun heq => hn (heq ▸ hown (by simp))
    have qp : q≠L.parity := fun heq => hn (heq ▸ hparityOwn)
    have qq : q≠L.q := fun heq => hn (heq ▸ hown (by simp))
    rw [prep.2.2.2.2 q qa qp qq]
    exact hready q hq hn
  have inv := L.windowStep_roundtrip hv out w A C D resize hp z zero carry hn hz hc hrow hown
    hbefore hafter hborrow st frozen hf v (m.drop (measurementCount (L.mintControls frozenWire zsign))) n
    ((keep L.u (by simp)).trans hu) ((keep L.k (by simp)).trans hk) va vq vb ve hzero hg hgv hfv ready hfit
  rw [taggedWindow,run_append,run_take,taggedWindowInverse,run_append,run_take,inv]
  exact run_reverse_proper _ (L.mintControls_proper frozenWire zsign tagvalid fa) s m _

theorem RoutedBankLayout.taggedWindow_spec (L : RoutedBankLayout) (hv : L.Valid)
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
    (st : ECDSAAdd.Divsteps.ZState) (frozen : Bool) (hf : st.f%2=1)
    (s : State) (m : List Bool) (hfreeze : s.basis frozenWire=frozen)
    (hzval : signedRegValue z s.basis=st.z) (hu : s.basis L.u=false) (hk : s.basis L.k=false)
    (ha0 : s.basis L.active=false) (hq0 : s.basis L.q=false) (hb0 : s.basis L.parity=false)
    (he : L.before.Encodes s.basis st) (hzero : frozen=true → st.g=0)
    (hg : frozen=false → PayloadFits (L.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep st).g))
    (hgv : frozen=false → PayloadFits (L.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep st).gv)
    (hfv : frozen=false → PayloadFits (L.vmid.length+1) (ECDSAAdd.Divsteps.zStep st).fv)
    (hready : A.Ready s.basis) (hfit : w.Fits (if frozen then st else ECDSAAdd.Divsteps.zStep st)) :
    let t := run (L.taggedWindow frozenWire zsign resize zero z carry) m s
    t.phase=s.phase ∧ C.Ready t.basis ∧
    out.Encodes t.basis (if frozen then st else ECDSAAdd.Divsteps.zStep st) ∧ out.Widths w ∧
    regValue z t.basis=counterWord z.length (!frozen) (decide (0≤st.z ∧ st.g%2=1)) (regValue z s.basis) ∧
    t.basis L.active= !frozen ∧ t.basis L.q=decide (0≤st.z ∧ st.g%2=1) ∧
    t.basis L.parity=decide (ECDSAAdd.Divsteps.bbit st=1) ∧
    (∀ q∈A.live,q∉L.before.rows.flatMap WindowRow.wires → q∉z →
      q≠L.active → q≠L.parity → q≠L.q → t.basis q=s.basis q) := by
  have tagvalid : [zsign,L.glow,L.parity,L.q].Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp htag).2).2
  have fa : frozenWire≠L.active := by simp_all
  have activeSep : L.active∉[zsign,L.glow,L.parity,L.q] :=
    (List.nodup_cons.mp (List.nodup_cons.mp htag).2).1
  let v := run (L.mintControls frozenWire zsign) m s
  have prep := L.mintControls_run frozenWire zsign tagvalid fa activeSep st zlo s m ha0 hb0 hq0
    (by simpa only [←hzview] using hzval) he.2.1
  have keep (q : Wire) (hq : q∈L.u::L.k::(L.before.rows.flatMap WindowRow.wires++z)) :
      v.basis q=s.basis q := by
    obtain ⟨a,b,c⟩ := hprepaway q hq
    exact prep.2.2.2.2 q a b c
  have ve : L.before.Encodes v.basis st := L.before.encodes_congr s.basis v.basis st he
    (fun q hq => keep q (by simp [hq]))
  have va : v.basis L.active= !frozen := prep.2.1.trans (congrArg Bool.not hfreeze)
  have vq : v.basis L.q=decide (0≤st.z ∧ st.g%2=1) := prep.2.2.2.1
  have vb : v.basis L.parity=decide (ECDSAAdd.Divsteps.bbit st=1) := by
    rw [prep.2.2.1]
    unfold ECDSAAdd.Divsteps.parityControl ECDSAAdd.Divsteps.bbit
    split_ifs <;> simp_all
  have ready : A.Ready v.basis := by
    intro q hq hn
    have qa : q≠L.active := fun heq => hn (heq ▸ hown (by simp))
    have qp : q≠L.parity := fun heq => hn (heq ▸ hparityOwn)
    have qq : q≠L.q := fun heq => hn (heq ▸ hown (by simp))
    rw [prep.2.2.2.2 q qa qp qq]
    exact hready q hq hn
  let ms := m.drop (measurementCount (L.mintControls frozenWire zsign))
  have rows := L.windowStep_rows hv out w A C D resize hp z zero carry hn hz hc hrow hown
    hbefore hafter hout hborrow st frozen hf v ms ((keep L.u (by simp)).trans hu)
    ((keep L.k (by simp)).trans hk) va vq vb ve hzero hg hgv hfv ready hfit
  have frame := L.windowStep_phase_frame hv out w A C D resize hp z zero carry hn hz hc hrow
    hborrow st frozen hf v ms ((keep L.u (by simp)).trans hu)
    ((keep L.k (by simp)).trans hk) va vq vb ve hzero hg hgv hfv ready hfit
  have ctrl (q : Wire) (hmem : q∈[L.active,L.parity,L.q]) :
      (run (L.windowStep resize zero z carry) ms v).basis q=v.basis q := by
    have own : q∈A.live := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hown (by simp)
      · exact hparityOwn
      · exact hown (by simp)
    have away : q∉L.before.rows.flatMap WindowRow.wires ∧ q∉z := by
      constructor <;> intro hq
      all_goals
        have hs := hprepaway q (by simp [hq])
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h | h | h
        · exact hs.1 h
        · exact hs.2.1 h
        · exact hs.2.2 h
    exact frame.2 q own away.1 away.2
  dsimp only
  rw [taggedWindow,run_append,run_take]
  refine ⟨frame.1.trans prep.1,rows.1,rows.2.1,rows.2.2.1,?_,
    (ctrl L.active (by simp)).trans va,(ctrl L.q (by simp)).trans vq,
    (ctrl L.parity (by simp)).trans vb,?_⟩
  · rw [rows.2.2.2,va,vq]
    rw [regValue_congr z v.basis s.basis (fun q hq => keep q (by simp [hq]))]
  · intro q hq hr hz qa qp qq
    exact (frame.2 q hq hr hz).trans (prep.2.2.2.2 q qa qp qq)

end ECDSAAdd.Arithmetic.Paper935
