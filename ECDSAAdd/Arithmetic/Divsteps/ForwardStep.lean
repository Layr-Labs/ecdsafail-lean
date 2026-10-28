import ECDSAAdd.Arithmetic.Divsteps.DataStep

set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- One physical forward divstep, including fresh full-word controls. The three
control outputs are retained as history for a later reversible schedule. -/
def forwardStep (q parity cin active glow gsign vlow vsign one zsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry cz z cc : List Wire) (bs : List ZeroBit) : Program :=
  prepareControls one active zsign glow parity q bs ++
    dataStep q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc

private theorem signed_congr (xs : List Wire) (s t : BasisState)
    (h : ∀ w, w∈xs → s w=t w) : signedRegValue xs s=signedRegValue xs t := by
  unfold signedRegValue
  rw [regValue_congr xs s t h]

theorem forwardStep_zSlot_controls (q parity cin active glow gsign vlow vsign one zsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry cz z cc zlo : List Wire) (bs : List ZeroBit)
    (hact : (one::active::bs.flatMap ZeroBit.wires).Nodup)
    (htags : [active,zsign,glow,parity,q].Nodup)
    (hinputs : bs.map ZeroBit.input=glow::(gmid++[gsign]))
    (hzlayout : zlo++[zsign]=z)
    (htagaway : List.Disjoint [active,parity,q]
      (f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++
        gmask++gcarry++vmask++vcarry++cz++z++cc++[cin]))
    (hctnd : (active::q::(cz++z++cc)).Nodup)
    (hctz : cz.length=z.length) (hctc : cc.length+1=z.length) (hctw : 2≤z.length)
    (hctaway : List.Disjoint (active::q::(cz++z++cc))
      (f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv))
    (hrnd : (q::((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv))).Nodup)
    (hrfg : f.length=(glow::(gmid++[gsign])).length)
    (hrvv : (vlow::(vmid++[vsign])).length=gv.length)
    (hrwork : List.Disjoint (parity::cin::active::(gmask++gcarry++vmask++vcarry))
      ((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv)))
    (hgnd : (q::parity::cin::(f++gmask++(glow::(gmid++[gsign]))++gcarry)).Nodup)
    (hvnd : (q::parity::cin::((vlow::(vmid++[vsign]))++vmask++gv++vcarry)).Nodup)
    (hdnd : (active::vlow::(vmid++[vsign])).Nodup)
    (hvd : List.Disjoint (vlow::(vmid++[vsign])) gv) (hav : active∉gv)
    (hsep : List.Disjoint (glow::(gmid++[gsign]))
      (q::parity::cin::active::((vlow::(vmid++[vsign]))++vmask++gv++vcarry)))
    (hfsep : List.Disjoint f ((vlow::(vmid++[vsign]))++gv))
    (hgs : f.length=gmask.length) (hgt : gmask.length=gmid.length+2)
    (hgc : gcarry.length+1=gmid.length+2)
    (hvs : (vlow::(vmid++[vsign])).length=vmask.length)
    (hvt : vmask.length=gv.length) (hvc : vcarry.length+1=gv.length)
    (st : ZState) (pB zB cB : Int) (hbnd : Bounds pB zB cB st) (hodd : st.f%2=1)
    (hgfit : 2*pB<((2^(gmid.length+1):Nat):Int))
    (hvfit : 2*cB<((2^(gv.length-1):Nat):Int))
    (hzfit : zB+1<((2^(z.length-1):Nat):Int))
    (s : State) (m : List Bool)
    (hone : s.basis one=false) (hwork : ∀ b∈bs,s.basis b.work=false)
    (hq : s.basis q=false) (hp : s.basis parity=false)
    (ha : s.basis active=false) (hi : s.basis cin=false)
    (hf : signedRegValue f s.basis=st.f)
    (hg : signedRegValue (glow::(gmid++[gsign])) s.basis=st.g)
    (hvf : signedRegValue (vlow::(vmid++[vsign])) s.basis=st.fv)
    (hvg : signedRegValue gv s.basis=st.gv)
    (hgm : regValue gmask s.basis=0) (hgk : regValue gcarry s.basis=0)
    (hcz : regValue cz s.basis=0) (hzz : signedRegValue z s.basis=st.z)
    (hcc : regValue cc s.basis=0)
    (hvm : regValue vmask s.basis=0) (hvk : regValue vcarry s.basis=0) :
    (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).phase=s.phase ∧
    signedRegValue f (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis=(zSlot st).f ∧
    signedRegValue (skywalkHalfView glow (gmid++[gsign])) (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis=(zSlot st).g ∧
    signedRegValue (vlow::(vmid++[vsign])) (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis=(zSlot st).fv ∧
    signedRegValue gv (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis=(zSlot st).gv ∧
    signedRegValue z (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis=(zSlot st).z ∧
    (∀ w, w∉active::parity::q::(f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z) →
      (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis w=s.basis w) ∧
    (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis active=activeControl st ∧
    (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis parity=parityControl st ∧
    (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis q=swapControl st := by
  let a := prepareControls one active zsign glow parity q bs
  let t := run a m s
  let rest := m.drop (measurementCount a)
  have ht : t=⟨s.phase,writeBit (writeBit (writeBit s.basis active (activeControl st))
      parity (parityControl st)) q (swapControl st)⟩ :=
    prepareControls_correct one active zsign glow parity q bs zlo (gmid++[gsign])
      hact htags hinputs st s m hone ha hp hq hwork (by rwa [hzlayout]) hg
  have keepTag (w : Wire) (hw : w∉[active,parity,q]) : t.basis w=s.basis w := by
    have hwa : w≠active := by intro hh; apply hw; simp [hh]
    have hwp : w≠parity := by intro hh; apply hw; simp [hh]
    have hwq : w≠q := by intro hh; apply hw; simp [hh]
    simp [ht,writeBit,hwa,hwp,hwq]
  have keep (w : Wire) (hw : w∈f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++
      gmask++gcarry++vmask++vcarry++cz++z++cc++[cin]) : t.basis w=s.basis w :=
    keepTag w (fun hh => List.disjoint_left.mp htagaway hh hw)
  have hap : t.phase=s.phase := by simp [ht]
  have haq : active≠q := by intro hh; subst q; simp at htags
  have hapar : active≠parity := by intro hh; subst parity; simp at htags
  have hpq : parity≠q := by intro hh; subst q; simp at htags
  have ka : t.basis active=activeControl st := by simp [ht,writeBit,haq,hapar]
  have kp : t.basis parity=parityControl st := by simp [ht,writeBit,hpq]
  have kq : t.basis q=swapControl st := by simp [ht,writeBit]
  have ki := keep cin (by simp)
  have kf := signed_congr f t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_append]; tauto))
  have kg := signed_congr (glow::(gmid++[gsign])) t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_append]; tauto))
  have kfv := signed_congr (vlow::(vmid++[vsign])) t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_append]; tauto))
  have kgv := signed_congr gv t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_append]; tauto))
  have kz := signed_congr z t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_append]; tauto))
  have kgm := regValue_congr gmask t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_append]; tauto))
  have kgk := regValue_congr gcarry t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_append]; tauto))
  have kvm := regValue_congr vmask t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_append]; tauto))
  have kvk := regValue_congr vcarry t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_append]; tauto))
  have kcz := regValue_congr cz t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_append]; tauto))
  have kcc := regValue_congr cc t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_append]; tauto))
  obtain ⟨hbp,hbf,hbg,hbfv,hbgv,hbz,hframe⟩ := dataStep_zSlot q parity cin active glow gsign vlow vsign
    f gmid gmask gcarry vmid vmask gv vcarry cz z cc hctnd hctz hctc hctw hctaway
    hrnd hrfg hrvv hrwork hgnd hvnd hdnd hvd hav hsep hfsep hgs hgt hgc hvs hvt hvc
    st pB zB cB hbnd hodd hgfit hvfit hzfit t rest kq kp ka (ki.trans hi)
    (kf.trans hf) (kg.trans hg) (kfv.trans hvf) (kgv.trans hvg)
    (kgm.trans hgm) (kgk.trans hgk) (kcz.trans hcz) (kz.trans hzz) (kcc.trans hcc)
    (kvm.trans hvm) (kvk.trans hvk)
  rw [forwardStep,run_append,run_take]
  have hn (c : Wire) (hc : c∈[active,parity,q]) :
      c∉f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z := by
    intro hh
    apply List.disjoint_left.mp htagaway hc
    simp only [List.mem_append] at hh ⊢
    tauto
  refine ⟨hbp.trans hap,hbf,hbg,hbfv,hbgv,hbz,?_,
    (hframe active (hn active (by simp))).trans ka,
    (hframe parity (hn parity (by simp))).trans kp,
    (hframe q (hn q (by simp))).trans kq⟩
  intro w hw
  have hrout : w∉f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z := by
    intro hh; apply hw; simp only [List.mem_cons]; tauto
  have htout : w∉[active,parity,q] := by
    intro hh; apply hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hh ⊢; tauto
  exact (hframe w hrout).trans (keepTag w htout)

theorem forwardStep_zSlot (q parity cin active glow gsign vlow vsign one zsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry cz z cc zlo : List Wire) (bs : List ZeroBit)
    (hact : (one::active::bs.flatMap ZeroBit.wires).Nodup)
    (htags : [active,zsign,glow,parity,q].Nodup)
    (hinputs : bs.map ZeroBit.input=glow::(gmid++[gsign]))
    (hzlayout : zlo++[zsign]=z)
    (htagaway : List.Disjoint [active,parity,q]
      (f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++
        gmask++gcarry++vmask++vcarry++cz++z++cc++[cin]))
    (hctnd : (active::q::(cz++z++cc)).Nodup)
    (hctz : cz.length=z.length) (hctc : cc.length+1=z.length) (hctw : 2≤z.length)
    (hctaway : List.Disjoint (active::q::(cz++z++cc))
      (f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv))
    (hrnd : (q::((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv))).Nodup)
    (hrfg : f.length=(glow::(gmid++[gsign])).length)
    (hrvv : (vlow::(vmid++[vsign])).length=gv.length)
    (hrwork : List.Disjoint (parity::cin::active::(gmask++gcarry++vmask++vcarry))
      ((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv)))
    (hgnd : (q::parity::cin::(f++gmask++(glow::(gmid++[gsign]))++gcarry)).Nodup)
    (hvnd : (q::parity::cin::((vlow::(vmid++[vsign]))++vmask++gv++vcarry)).Nodup)
    (hdnd : (active::vlow::(vmid++[vsign])).Nodup)
    (hvd : List.Disjoint (vlow::(vmid++[vsign])) gv) (hav : active∉gv)
    (hsep : List.Disjoint (glow::(gmid++[gsign]))
      (q::parity::cin::active::((vlow::(vmid++[vsign]))++vmask++gv++vcarry)))
    (hfsep : List.Disjoint f ((vlow::(vmid++[vsign]))++gv))
    (hgs : f.length=gmask.length) (hgt : gmask.length=gmid.length+2)
    (hgc : gcarry.length+1=gmid.length+2)
    (hvs : (vlow::(vmid++[vsign])).length=vmask.length)
    (hvt : vmask.length=gv.length) (hvc : vcarry.length+1=gv.length)
    (st : ZState) (pB zB cB : Int) (hbnd : Bounds pB zB cB st) (hodd : st.f%2=1)
    (hgfit : 2*pB<((2^(gmid.length+1):Nat):Int))
    (hvfit : 2*cB<((2^(gv.length-1):Nat):Int))
    (hzfit : zB+1<((2^(z.length-1):Nat):Int))
    (s : State) (m : List Bool)
    (hone : s.basis one=false) (hwork : ∀ b∈bs,s.basis b.work=false)
    (hq : s.basis q=false) (hp : s.basis parity=false)
    (ha : s.basis active=false) (hi : s.basis cin=false)
    (hf : signedRegValue f s.basis=st.f)
    (hg : signedRegValue (glow::(gmid++[gsign])) s.basis=st.g)
    (hvf : signedRegValue (vlow::(vmid++[vsign])) s.basis=st.fv)
    (hvg : signedRegValue gv s.basis=st.gv)
    (hgm : regValue gmask s.basis=0) (hgk : regValue gcarry s.basis=0)
    (hcz : regValue cz s.basis=0) (hzz : signedRegValue z s.basis=st.z)
    (hcc : regValue cc s.basis=0)
    (hvm : regValue vmask s.basis=0) (hvk : regValue vcarry s.basis=0) :
    (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).phase=s.phase ∧
    signedRegValue f (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis=(zSlot st).f ∧
    signedRegValue (skywalkHalfView glow (gmid++[gsign])) (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis=(zSlot st).g ∧
    signedRegValue (vlow::(vmid++[vsign])) (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis=(zSlot st).fv ∧
    signedRegValue gv (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis=(zSlot st).gv ∧
    signedRegValue z (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis=(zSlot st).z ∧
    (∀ w, w∉active::parity::q::(f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z) →
      (run (forwardStep q parity cin active glow gsign vlow vsign one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs) m s).basis w=s.basis w) := by
  obtain ⟨phase,f',g',fv',gv',z',frame,_,_,_⟩ := forwardStep_zSlot_controls q parity cin active glow gsign vlow vsign one zsign
    f gmid gmask gcarry vmid vmask gv vcarry cz z cc zlo bs
    hact htags hinputs hzlayout htagaway hctnd hctz hctc hctw hctaway
    hrnd hrfg hrvv hrwork hgnd hvnd hdnd hvd hav hsep hfsep hgs hgt hgc hvs hvt hvc
    st pB zB cB hbnd hodd hgfit hvfit hzfit s m hone hwork hq hp ha hi
    hf hg hvf hvg hgm hgk hcz hzz hcc hvm hvk
  exact ⟨phase,f',g',fv',gv',z',frame⟩

/-- Exact static gate and measurement totals for this same composed program.
They include full-word activity detection and counter update, even when frozen. -/
theorem forwardStep_counts (q parity cin active glow gsign vlow vsign one zsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry cz z cc : List Wire) (bs : List ZeroBit)
    (hrnd : (q::((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv))).Nodup)
    (hrfg : f.length=(glow::(gmid++[gsign])).length)
    (hrvv : (vlow::(vmid++[vsign])).length=gv.length)
    (hinputs : bs.map ZeroBit.input=glow::(gmid++[gsign]))
    (hgs : f.length=gmask.length) (hgt : gmask.length=gmid.length+2)
    (hgc : gcarry.length+1=gmid.length+2)
    (hvs : (vlow::(vmid++[vsign])).length=vmask.length)
    (hvt : vmask.length=gv.length) (hvc : vcarry.length+1=gv.length)
    (hctz : cz.length=z.length) (hctc : cc.length+1=z.length) :
    toffoliCount (forwardStep q parity cin active glow gsign vlow vsign one zsign
      f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs)=
        5*(gmid.length+2)+5*(vmid.length+2)+z.length-4 ∧
    measurementCount (forwardStep q parity cin active glow gsign vlow vsign one zsign
      f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs)=
        4*(gmid.length+2)+3*(vmid.length+2)+z.length-5 := by
  obtain ⟨pt,pm⟩ := prepareControls_counts one active zsign glow parity q bs
  obtain ⟨rt,rm⟩ := routeRows_counts q f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv hrfg hrvv hrnd
  obtain ⟨bt,bm⟩ := rowBody_counts q parity cin active glow gsign vlow vsign
    f gmid gmask gcarry vmid vmask gv vcarry hgs hgt hgc hvs hvt hvc
  obtain ⟨ct,cm⟩ := counterUpdate_counts active q cz z cc hctz hctc
  have hbl := congrArg List.length hinputs
  simp only [List.length_map,List.length_cons,List.length_append,List.length_nil] at hbl hrfg hrvv
  simp only [forwardStep,dataStep,routedBody,toffoliCount_append,measurementCount_append,
    pt,pm,rt,rm,bt,bm,ct,cm,List.length_cons,List.length_append,List.length_nil]
  omega

/-- Static support as a set, so overlapping reusable workspace is counted only
once. No concrete allocation or net space improvement is asserted here. -/
def forwardStepSupport (q parity cin active glow gsign vlow vsign one zsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry cz z cc : List Wire) (bs : List ZeroBit) : Finset Wire :=
  (one::active::zsign::glow::parity::q::cin::gsign::vlow::vsign::
    (f++gmid++gmask++gcarry++vmid++vmask++gv++vcarry++cz++z++cc++bs.flatMap ZeroBit.wires)).toFinset

theorem forwardStep_wires_subset (q parity cin active glow gsign vlow vsign one zsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry cz z cc : List Wire) (bs : List ZeroBit)
    (hrfg : f.length=(glow::(gmid++[gsign])).length)
    (hrvv : (vlow::(vmid++[vsign])).length=gv.length)
    (hgs : f.length=gmask.length) (hgt : gmask.length=gmid.length+2)
    (hgc : gcarry.length+1=gmid.length+2)
    (hvs : (vlow::(vmid++[vsign])).length=vmask.length)
    (hvt : vmask.length=gv.length) (hvc : vcarry.length+1=gv.length)
    (hctz : cz.length=z.length) (hctc : cc.length+1=z.length) :
    wires (forwardStep q parity cin active glow gsign vlow vsign one zsign
      f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs)⊆
    forwardStepSupport q parity cin active glow gsign vlow vsign one zsign
      f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs := by
  intro w hw
  simp only [forwardStep,prepareControls,dataStep,routedBody,rowBody,coefficientPair,
    wires_append,Finset.mem_union] at hw
  rcases hw with (ha|hb)|((hr|(hh|(hk|hd)))|hc)
  · rw [activityTag_wires] at ha
    simp only [forwardStepSupport,List.mem_toFinset,List.mem_cons,List.mem_append] at ha ⊢
    tauto
  · rw [(branchTags_resources zsign glow parity q).2.2] at hb
    simp only [forwardStepSupport,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hb ⊢
    tauto
  · have hh := swapRegisters_wires q (f++(vlow::(vmid++[vsign])))
      ((glow::(gmid++[gsign]))++gv) (by simp only [List.length_append,hrfg,hrvv]) hr
    simp only [forwardStepSupport,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hh ⊢
    tauto
  · rw [halfRow_wires q parity cin glow gsign f gmask gmid gcarry hgs hgt hgc] at hh
    simp only [forwardStepSupport,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hh ⊢
    tauto
  · rw [rowKernel_wires q parity cin (vlow::(vmid++[vsign])) vmask gv vcarry hvs hvt hvc] at hk
    simp only [forwardStepSupport,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hk ⊢
    tauto
  · rw [doubleSigned_wires] at hd
    simp only [forwardStepSupport,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hd ⊢
    tauto
  · have hh := counterUpdate_wires_subset active q cz z cc hctz hctc hc
    simp only [forwardStepSupport,List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
    tauto

theorem forwardStep_qubits (q parity cin active glow gsign vlow vsign one zsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry cz z cc : List Wire) (bs : List ZeroBit)
    (hrfg : f.length=(glow::(gmid++[gsign])).length)
    (hrvv : (vlow::(vmid++[vsign])).length=gv.length)
    (hgs : f.length=gmask.length) (hgt : gmask.length=gmid.length+2)
    (hgc : gcarry.length+1=gmid.length+2)
    (hvs : (vlow::(vmid++[vsign])).length=vmask.length)
    (hvt : vmask.length=gv.length) (hvc : vcarry.length+1=gv.length)
    (hctz : cz.length=z.length) (hctc : cc.length+1=z.length) :
    qubitCount (forwardStep q parity cin active glow gsign vlow vsign one zsign
      f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs)≤
    (forwardStepSupport q parity cin active glow gsign vlow vsign one zsign
      f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs).card := by
  exact Finset.card_le_card (forwardStep_wires_subset q parity cin active glow gsign vlow vsign
    one zsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc bs hrfg hrvv hgs hgt hgc
    hvs hvt hvc hctz hctc)

end ECDSAAdd.Arithmetic.Divsteps
