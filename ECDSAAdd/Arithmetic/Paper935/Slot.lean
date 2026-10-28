import ECDSAAdd.Arithmetic.Paper935.SlotBody
import ECDSAAdd.Arithmetic.Paper935.PublicPost

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

private theorem pin_rows (tmin t : Nat) (u : PinState) :
    (pinStep tmin t u).rows=(if u.frozen then u.rows else ECDSAAdd.Divsteps.zStep u.rows) := by
  unfold pinStep
  split_ifs
  · rfl
  · dsimp only
    split_ifs <;> rfl

def slot (tmin index : Nat) (one zf fire witness frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) (bs rb : List ZeroBit) : Program :=
  slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry ++
    publicPost (decide (tmin ≤ index)) one zf frozen fire active witness bs rb (index+1-tmin)

theorem slot_spec (tmin index : Nat) (one zf fire witness frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry zlo : List Wire) (bs rb : List ZeroBit)
    (hn1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).Nodup)
    (hn2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).Nodup)
    (hgn : (glow::(gmid++[gsign])).Nodup)
    (hvn : (active::vlow::(vmid++[vsign])).Nodup)
    (hsep : List.Disjoint (glow::(gmid++[gsign])) ((vlow::(vmid++[vsign]))++gv))
    (hvs : List.Disjoint (vlow::(vmid++[vsign])) ((glow::(gmid++[gsign]))++gv))
    (hac : active∉(glow::(gmid++[gsign]))++gv)
    (hl1 : f.length=gmid.length+2) (hl2 : gv.length=vmid.length+2)
    (hr : (q::((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv))).Nodup)
    (hcontrols : List.Disjoint [q,parity,u,k,active]
      (f++(vlow::(vmid++[vsign]))++(glow::(gmid++[gsign]))++gv))
    (hfs : List.Disjoint f ((glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv))
    (hcn : (active::q::(zero++z++carry)).Nodup)
    (hzero : zero.length=z.length) (hcarry : carry.length+1=z.length)
    (hwidth : 2≤z.length)
    (hcounter : List.Disjoint (active::q::(zero++z++carry))
      (f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv))
    (hzview : z=zlo++[zsign])
    (htn : [zsign,glow,parity,q].Nodup)
    (htsep : List.Disjoint [q,parity]
      (u::k::active::(zero++carry++z++f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv)))
    (hakeep : active∉q::parity::u::k::(zero++carry++z++f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv))
    (hfreeze : frozen∉active::q::parity::(f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z))
    (st : ECDSAAdd.Divsteps.ZState) (hf : st.f%2=1) (s : State) (m : List Bool)
    (hz0 : regValue zero s.basis=0) (hcarry0 : regValue carry s.basis=0)
    (hzval : signedRegValue z s.basis=st.z)
    (hzlo : s.basis frozen=false → -((2^(z.length-1):Nat):Int)≤(ECDSAAdd.Divsteps.zStep st).z)
    (hzhi : s.basis frozen=false → (ECDSAAdd.Divsteps.zStep st).z<((2^(z.length-1):Nat):Int))
    (hu : s.basis u=false) (hk : s.basis k=false) (hacle : s.basis active=false)
    (hq0 : s.basis q=false) (hp0 : s.basis parity=false)
    (ha : signedRegValue f s.basis=st.f)
    (hb : signedRegValue (glow::(gmid++[gsign])) s.basis=st.g)
    (hx : signedRegValue (vlow::(vmid++[vsign])) s.basis=st.fv)
    (hy : signedRegValue gv s.basis=st.gv)
    (hlo1 : s.basis frozen=false → -((2^(gmid.length+1):Nat):Int)≤2*(ECDSAAdd.Divsteps.zStep st).g)
    (hhi1 : s.basis frozen=false → 2*(ECDSAAdd.Divsteps.zStep st).g<((2^(gmid.length+1):Nat):Int))
    (hlo2 : s.basis frozen=false → -((2^(gv.length-1):Nat):Int)≤(ECDSAAdd.Divsteps.zStep st).gv)
    (hhi2 : s.basis frozen=false → (ECDSAAdd.Divsteps.zStep st).gv<((2^(gv.length-1):Nat):Int))
    (hlo3 : s.basis frozen=false → -((2^(vmid.length+1):Nat):Int)≤(ECDSAAdd.Divsteps.zStep st).fv)
    (hhi3 : s.basis frozen=false → (ECDSAAdd.Divsteps.zStep st).fv<((2^(vmid.length+1):Nat):Int))
    (hfgzero : s.basis frozen=true → st.g=0)
    (hprobe : (one::zf::bs.flatMap ZeroBit.wires).Nodup)
    (hrn : (rb.map ZeroBit.input).Nodup) (hzf : zf≠frozen) (hfirefrozen : fire≠frozen)
    (hfirer : fire∉rb.map ZeroBit.input) (hfrozenr : frozen∉rb.map ZeroBit.input)
    (hoffset : index≥tmin → index+1-tmin<2^(rb.map ZeroBit.input).length)
    (hafire : active≠fire) (har : active∉rb.map ZeroBit.input) (hazf : active≠zf)
    (hzfire : zf≠fire) (hzrecord : zf∉rb.map ZeroBit.input)
    (hstable : ∀ w∈one::bs.flatMap ZeroBit.wires,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉rb.map ZeroBit.input)
    (hone : s.basis one=true) (hzc : s.basis zf=false) (hfire0 : s.basis fire=false)
    (hwork : ∀ b∈bs,s.basis b.work=false)
    (hlt : index≥tmin → regValue (rb.map ZeroBit.input) s.basis < index+1-tmin)
    (hrecord : s.basis frozen=false → regValue (rb.map ZeroBit.input) s.basis=0)
    (hcnd : (one::witness::rb.flatMap ZeroBit.wires).Nodup)
    (hwf : witness≠fire) (hfw : frozen≠witness) (hfirework : fire∉rb.map ZeroBit.work)
    (hcleanframe : ∀ w∈witness::rb.map ZeroBit.work,
      w≠active ∧ w≠fire ∧ w≠frozen ∧ w∉rb.map ZeroBit.input)
    (hw : s.basis witness=false) (hcw : ∀ b∈rb,s.basis b.work=false)
    (hprobeview : bs.map ZeroBit.input=skywalkHalfView glow (gmid++[gsign]))
    (hreads : ∀ w∈one::zf::fire::witness::(rb.map ZeroBit.input++bs.map ZeroBit.work++rb.map ZeroBit.work),
      w∉active::q::parity::(f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z))
    (hpostrows : ∀ w∈f++skywalkHalfView glow (gmid++[gsign])++(vlow::(vmid++[vsign]))++gv++z,
      w≠active ∧ w≠frozen ∧ w∉rb.map ZeroBit.input) :
    let old : PinState := ⟨st,s.basis frozen,regValue (rb.map ZeroBit.input) s.basis⟩
    let next := pinStep tmin index old
    let t := run (slot tmin index one zf fire witness frozen q parity u k active glow gsign vlow vsign zsign
      f gmid vmid gv zero z carry bs rb) m s
    t.phase=s.phase ∧ t.basis active=false ∧ t.basis zf=false ∧ t.basis fire=false ∧
      t.basis frozen=next.frozen ∧ regValue (rb.map ZeroBit.input) t.basis=next.offset ∧
      (∀ w,w≠frozen → w∉rb.map ZeroBit.input →
        w∉q::parity::(f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z) → t.basis w=s.basis w) ∧
      signedRegValue z t.basis=next.rows.z ∧ signedRegValue f t.basis=next.rows.f ∧
      signedRegValue (skywalkHalfView glow (gmid++[gsign])) t.basis=next.rows.g ∧
      signedRegValue (vlow::(vmid++[vsign])) t.basis=next.rows.fv ∧
      signedRegValue gv t.basis=next.rows.gv := by
  let body := slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry
  let v := run body m s
  let ms := m.drop (measurementCount body)
  let nextRows := if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st
  have h := slotBody_spec frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry zlo
    hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 hr hcontrols hfs hcn hzero hcarry hwidth hcounter hzview htn htsep
    hakeep hfreeze st hf s m hz0 hcarry0 hzval hzlo hzhi hu hk hacle hq0 hp0 ha hb hx hy
    hlo1 hhi1 hlo2 hhi2 hlo3 hhi3 hfgzero
  have frame := h.2.2.2.1
  have keep (w : Wire)
      (hw : w∈one::zf::fire::witness::(rb.map ZeroBit.input++bs.map ZeroBit.work++rb.map ZeroBit.work)) :
      v.basis w=s.basis w := frame w (hreads w hw)
  have recordeq : regValue (rb.map ZeroBit.input) v.basis=regValue (rb.map ZeroBit.input) s.basis := by
    apply regValue_congr
    intro w hw
    exact keep w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hw))))))
  have vwork : ∀ b∈bs,v.basis b.work=false := by
    intro b hb
    refine (keep b.work ?_).trans (hwork b hb)
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨b,hb,rfl⟩))))))
  have vcw : ∀ b∈rb,v.basis b.work=false := by
    intro b hb
    refine (keep b.work ?_).trans (hcw b hb)
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨b,hb,rfl⟩)))))
  have haz : active≠frozen := Ne.symm (fun hh => hfreeze (by simp [hh]))
  have hp := publicPost_spec (decide (tmin ≤ index)) one zf frozen fire active witness bs rb (index+1-tmin)
    hprobe hrn hzf hfirefrozen hfirer hfrozenr (fun hh => hoffset (of_decide_eq_true hh))
    hafire haz har hazf hzfire hzrecord hstable v ms
    ((keep one (by simp)).trans hone) ((keep zf (by simp)).trans hzc) vwork
    ((keep fire (by simp)).trans hfire0) (by rw [h.2.1,h.2.2.1])
    (fun hh => by rw [recordeq]; exact hlt (of_decide_eq_true hh))
    (fun hh => by rw [recordeq]; exact hrecord (h.2.2.1 ▸ hh))
    hcnd hwf hfw hfirework hcleanframe ((keep witness (by simp)).trans hw) vcw
  have zeroeq : decide (regValue (bs.map ZeroBit.input) v.basis=0)=decide (nextRows.g=0) := by
    congr 1
    rw [←signedRegValue_zero_iff,hprobeview,h.2.2.2.2.2.2.1]
  have hflags := pinStep_flag_record tmin index
    (⟨st,s.basis frozen,regValue (rb.map ZeroBit.input) s.basis⟩ : PinState) hrecord
  have hrow (xs : List Wire)
      (hin : ∀ w∈xs,w∈f++skywalkHalfView glow (gmid++[gsign])++(vlow::(vmid++[vsign]))++gv++z) :
      signedRegValue xs (run (publicPost (decide (tmin ≤ index)) one zf frozen fire active witness bs rb (index+1-tmin)) ms v).basis=
        signedRegValue xs v.basis := by
    unfold signedRegValue
    apply congrArg
    apply regValue_congr
    intro w hw
    obtain ⟨h1,h2,h3⟩ := hpostrows w (hin w hw)
    exact hp.2.2.2.2.2.2 w h1 h2 h3
  dsimp only
  rw [slot,run_append,run_take]
  refine ⟨hp.1.trans h.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hp.2.2.2.2.1,h.2.2.1,zeroeq]
    simpa only [nextRows, apply_ite] using hflags.1.symm
  · rw [hp.2.2.2.2.2.1,recordeq,h.2.2.1,zeroeq]
    simpa only [nextRows, apply_ite] using hflags.2.symm
  · intro w hwf hwr hwb
    by_cases hwa : w=active
    · subst w; exact hp.2.1.trans hacle.symm
    · exact (hp.2.2.2.2.2.2 w hwa hwf hwr).trans
        (frame w (by rw [List.mem_cons]; exact fun hh => hh.elim hwa hwb))
  · rw [pin_rows]
    exact (hrow z (by intro w hw; exact List.mem_append_right _ hw)).trans h.2.2.2.2.1
  · rw [pin_rows]
    exact (hrow f (by intro w hw; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw))))).trans h.2.2.2.2.2.1
  · rw [pin_rows]
    exact (hrow (skywalkHalfView glow (gmid++[gsign])) (by intro w hw; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw))))).trans h.2.2.2.2.2.2.1
  · rw [pin_rows]
    exact (hrow (vlow::(vmid++[vsign])) (by intro w hw; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw)))).trans h.2.2.2.2.2.2.2.1
  · rw [pin_rows]
    exact (hrow gv (by intro w hw; exact List.mem_append_left _ (List.mem_append_right _ hw))).trans h.2.2.2.2.2.2.2.2

theorem slot_counts (tmin index : Nat)
    (one zf fire witness frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) (bs rb : List ZeroBit) :
    toffoliCount (slot tmin index one zf fire witness frozen q parity u k active glow gsign vlow vsign zsign
      f gmid vmid gv zero z carry bs rb)=
      toffoliCount (taggedStep q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry)+
        (if tmin ≤ index then 2*bs.length+1+2*rb.length else 0) ∧
    measurementCount (slot tmin index one zf fire witness frozen q parity u k active glow gsign vlow vsign zsign
      f gmid vmid gv zero z carry bs rb)=
      measurementCount (taggedStep q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry)+
        (if tmin ≤ index then 2*bs.length+(2*rb.length+1) else 0) := by
  have hb := slotBody_counts frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry
  have hp := publicPost_counts (decide (tmin ≤ index)) one zf frozen fire active witness bs rb (index+1-tmin)
  simp only [slot,toffoliCount_append,measurementCount_append,hb.1,hb.2,hp.1,hp.2,decide_eq_true_eq,and_self]

theorem slot_support (tmin index : Nat)
    (one zf fire witness frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) (bs rb : List ZeroBit) :
    wires (slot tmin index one zf fire witness frozen q parity u k active glow gsign vlow vsign zsign
      f gmid vmid gv zero z carry bs rb) ⊆
      wires (slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) ∪
        (one::zf::frozen::fire::active::witness::
          (rb.map ZeroBit.input++bs.flatMap ZeroBit.wires++rb.flatMap ZeroBit.wires)).toFinset := by
  rw [slot,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (publicPost_support _ _ _ _ _ _ _ _ _ _)

end ECDSAAdd.Arithmetic.Paper935
