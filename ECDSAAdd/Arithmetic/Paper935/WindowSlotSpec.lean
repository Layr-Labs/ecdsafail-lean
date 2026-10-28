import ECDSAAdd.Arithmetic.Paper935.WindowSlot
import ECDSAAdd.Arithmetic.Paper935.WindowSlotMath

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

private theorem control_separation (a b c d e f : Wire) (h : [a,b,c,d,e,f].Nodup) :
    a≠f ∧ b≠f ∧ a≠e ∧ b≠e := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,or_false,not_or] at h
  tauto

theorem RoutedBankLayout.windowSlot_spec (L : RoutedBankLayout) (hv : L.Valid)
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
    (P : WindowPostLayout) (pvalid : P.Valid) (pactive : P.active=L.active) (pfrozen : P.frozen=frozenWire)
    (persist : ∀ q∈P.one::P.frozen::P.recordWires,
      q∈A.live ∧ q∉L.before.rows.flatMap WindowRow.wires ∧ q∉z ∧
      q≠L.active ∧ q≠L.parity ∧ q≠L.q)
    (scratch : P.scratch.toFinset⊆arenaWires\C.live)
    (one : s.basis P.one=true)
    (oldOffset : P.armed=true → regValue P.recordWires s.basis<P.offset)
    (activeOffset : s.basis frozenWire=false → regValue P.recordWires s.basis=0)
    (tmin index : Nat) (armed : P.armed=decide (tmin ≤ index)) (offset : P.offset=index+1-tmin)
    (probeview : BlockedZero.inputs P.blocks=out.g.wires)
    (postrows : ∀ q∈out.rows.flatMap WindowRow.wires++z,q≠P.active ∧ q≠P.frozen ∧ q∉P.recordWires)
    (postown : (P.frozen::P.recordWires).toFinset⊆C.live)
    (zwidth : 2≤z.length)
    (zfit : PayloadFits (z.length-1) (if frozen then st else ECDSAAdd.Divsteps.zStep st).z) :
    let old : PinState := ⟨st,frozen,regValue P.recordWires s.basis⟩
    let next := pinStep tmin index old
    let t := run (L.windowSlot out P frozenWire zsign resize zero z carry) m s
    t.phase=s.phase ∧ C.Ready t.basis ∧ out.Encodes t.basis next.rows ∧
    signedRegValue z t.basis=next.rows.z ∧ t.basis P.frozen=next.frozen ∧
    regValue P.recordWires t.basis=next.offset ∧ t.basis P.active=false ∧ t.basis L.q=false ∧
    t.basis L.parity=decide (ECDSAAdd.Divsteps.bbit st=1) ∧ t.basis P.zf=false ∧ t.basis P.fire=false := by
  let old : PinState := ⟨st,frozen,regValue P.recordWires s.basis⟩
  let v := run (L.retiredWindow out frozenWire zsign resize zero z carry) m s
  let ms := m.drop (measurementCount (L.retiredWindow out frozenWire zsign resize zero z carry))
  have body := L.retiredWindow_spec hv out w A C D resize hp z zero carry hn hz hc hrow hown
    hbefore hafter hout hborrow frozenWire zsign zlo hzview htag hparityOwn hprepaway hrowq hsecond hwfv
    pmod st hi hpmod frozen hf s m hfreeze hzval hu hk ha0 hq0 hb0 he hzero hg hgv hfv hready hfit
  have ready := L.retiredWindow_post_ready hv out w A C D resize hp z zero carry hn hz hc hrow hown
    hbefore hafter hout hborrow frozenWire zsign zlo hzview htag hparityOwn hprepaway hrowq hsecond hwfv
    pmod st hi hpmod frozen hf s m hfreeze hzval hu hk ha0 hq0 hb0 he hzero hg hgv hfv hready hfit
    P pactive pfrozen persist scratch one oldOffset activeOffset
  have post := P.run_spec pvalid v ms ready
  have free := P.arena_ready_after pvalid C v ms ready body.2.1 postown
  have keep (q : Wire) (hq : q∈P.one::P.frozen::P.recordWires) : v.basis q=s.basis q := by
    obtain ⟨a,b,c,d,e,f⟩ := persist q hq
    exact body.2.2.2.2.2.2.2.2 q a b c d e f
  have recordeq : regValue P.recordWires v.basis=regValue P.recordWires s.basis :=
    regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))
  have frozenEq : v.basis P.frozen=frozen := by rw [keep P.frozen (by simp),pfrozen,hfreeze]
  have zeroeq : decide (regValue (BlockedZero.inputs P.blocks) v.basis=0)=
      decide ((if frozen then st else ECDSAAdd.Divsteps.zStep st).g=0) := by
    simp only [probeview,←signedRegValue_zero_iff]
    exact congrArg (fun x : Int => decide (x=0)) body.2.2.1.2.1
  have pin := pinStep_flag_record tmin index old (by
    intro h; exact activeOffset (hfreeze.trans h))
  have enc := out.encodes_congr v.basis (run P.program ms v).basis
    (if frozen then st else ECDSAAdd.Divsteps.zStep st) body.2.2.1 (by
      intro q hq
      obtain ⟨a,b,c⟩ := postrows q (List.mem_append_left _ hq)
      exact post.2.2.2.2.2.2 q a b c)
  have zkeep : signedRegValue z (run P.program ms v).basis=signedRegValue z v.basis := by
    unfold signedRegValue
    rw [regValue_congr z _ v.basis (by
      intro q hq
      obtain ⟨a,b,c⟩ := postrows q (List.mem_append_right _ hq)
      exact post.2.2.2.2.2.2 q a b c)]
  have zv : signedRegValue z v.basis=(if frozen then st else ECDSAAdd.Divsteps.zStep st).z := by
    change signedDecode z.length (regValue z v.basis)=_
    rw [body.2.2.2.2.1]
    exact pinnedCounter_value st frozen z.length (regValue z s.basis) zwidth (regValue_lt _ _) hzval hzero zfit
  have sep : frozenWire≠L.q ∧ L.active≠L.q ∧ frozenWire≠L.parity ∧ L.active≠L.parity := by
    exact control_separation frozenWire L.active zsign L.glow L.parity L.q htag
  have qpost : L.q≠P.active ∧ L.q≠P.frozen ∧ L.q∉P.recordWires := by
    refine ⟨?_,?_,?_⟩
    · rw [pactive]; exact sep.2.1.symm
    · rw [pfrozen]; exact sep.1.symm
    · intro h; exact (persist L.q (by simp [h])).2.2.2.2.2 rfl
  have bpost : L.parity≠P.active ∧ L.parity≠P.frozen ∧ L.parity∉P.recordWires := by
    refine ⟨?_,?_,?_⟩
    · rw [pactive]; exact sep.2.2.2.symm
    · rw [pfrozen]; exact sep.2.2.1.symm
    · intro h; exact (persist L.parity (by simp [h])).2.2.2.2.1 rfl
  dsimp only
  rw [windowSlot,run_append,run_take]
  refine ⟨post.1.trans body.1,free,?_,?_,?_,?_,post.2.1,?_,?_,post.2.2.1,post.2.2.2.1⟩
  · simpa only [pinStep_rows] using enc
  · rw [pinStep_rows]; exact zkeep.trans zv
  · rw [post.2.2.2.2.1,frozenEq,zeroeq,armed]
    cases frozen <;> simpa [old] using pin.1.symm
  · rw [post.2.2.2.2.2.1,recordeq,frozenEq,zeroeq,armed,offset]
    cases frozen <;> simpa [old] using pin.2.symm
  · exact (post.2.2.2.2.2.2 L.q qpost.1 qpost.2.1 qpost.2.2).trans body.2.2.2.2.2.2.1
  · exact (post.2.2.2.2.2.2 L.parity bpost.1 bpost.2.1 bpost.2.2).trans body.2.2.2.2.2.2.2.1

end ECDSAAdd.Arithmetic.Paper935
