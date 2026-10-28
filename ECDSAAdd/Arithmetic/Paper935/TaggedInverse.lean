import ECDSAAdd.Arithmetic.Paper935.ActiveInverse

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

theorem branchTags_proper (zsign glow parity swap : Wire)
    (hn : [zsign,glow,parity,swap].Nodup) : ProperProgram (branchTags zsign glow parity swap) := by
  have hgp : glow≠parity := by simp_all
  have hzq : zsign≠swap := by simp_all
  have hpq : parity≠swap := by simp_all
  simp [branchTags,ProperProgram,ProperGate,hgp,hzq,hpq]

def taggedStepInverse (q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) : Program :=
  activeStepInverse q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry ++
    (branchTags zsign glow parity q).reverse

theorem taggedStep_roundtrip (q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry zlo : List Wire)
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
    (hcounter : List.Disjoint (active::q::(zero++z++carry))
      (f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv))
    (hzview : z=zlo++[zsign])
    (htn : [zsign,glow,parity,q].Nodup)
    (htsep : List.Disjoint [q,parity]
      (u::k::active::(zero++carry++z++f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv)))
    (st : ECDSAAdd.Divsteps.ZState) (hf : st.f%2=1) (s : State) (m n : List Bool)
    (hz0 : regValue zero s.basis=0) (hcarry0 : regValue carry s.basis=0)
    (hzval : signedRegValue z s.basis=st.z)
    (hu : s.basis u=false) (hk : s.basis k=false) (halive : s.basis active=true)
    (hq0 : s.basis q=false) (hp0 : s.basis parity=false)
    (ha : signedRegValue f s.basis=st.f)
    (hb : signedRegValue (glow::(gmid++[gsign])) s.basis=st.g)
    (hx : signedRegValue (vlow::(vmid++[vsign])) s.basis=st.fv)
    (hy : signedRegValue gv s.basis=st.gv)
    (hlo1 : -((2^(gmid.length+1):Nat):Int)≤2*(ECDSAAdd.Divsteps.zStep st).g)
    (hhi1 : 2*(ECDSAAdd.Divsteps.zStep st).g<((2^(gmid.length+1):Nat):Int))
    (hlo2 : -((2^(gv.length-1):Nat):Int)≤(ECDSAAdd.Divsteps.zStep st).gv)
    (hhi2 : (ECDSAAdd.Divsteps.zStep st).gv<((2^(gv.length-1):Nat):Int))
    (hlo3 : -((2^(vmid.length+1):Nat):Int)≤(ECDSAAdd.Divsteps.zStep st).fv)
    (hhi3 : (ECDSAAdd.Divsteps.zStep st).fv<((2^(vmid.length+1):Nat):Int)) :
    run (taggedStepInverse q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) n
      (run (taggedStep q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s)=s := by
  let p := branchTags zsign glow parity q
  let v := run p m s
  have hp := branchTags_correct zsign glow parity q htn s m hp0 hq0
  have frame (w : Wire) (hwq : w≠q) (hwp : w≠parity) : v.basis w=s.basis w := by
    dsimp only [v,p]
    rw [hp]; simp [writeBit,hwq,hwp]
  have keep (w : Wire)
      (hw : w∈u::k::active::(zero++carry++z++f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv)) :
      v.basis w=s.basis w := by
    have hn := List.disjoint_right.mp htsep hw
    exact frame w (fun h => hn (by simp [h])) (fun h => hn (by simp [h]))
  have regs (xs : List Wire)
      (hxs : ∀ w∈xs,w∈u::k::active::(zero++carry++z++f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv)) :
      regValue xs v.basis=regValue xs s.basis :=
    regValue_congr xs _ _ (fun w hw => keep w (hxs w hw))
  have signed (xs : List Wire)
      (hxs : ∀ w∈xs,w∈u::k::active::(zero++carry++z++f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv)) :
      signedRegValue xs v.basis=signedRegValue xs s.basis := by
    unfold signedRegValue; rw [regs xs hxs]
  have tags := branchTags_zState zsign glow parity q zlo (gmid++[gsign]) htn st s m hp0 hq0
    (by simpa only [←hzview] using hzval) hb
  have hq : v.basis q=decide (0≤st.z ∧ st.g%2=1) := tags.2
  have hc : v.basis parity=decide (ECDSAAdd.Divsteps.bbit st=1) := by
    rw [tags.1]
    unfold ECDSAAdd.Divsteps.parityControl ECDSAAdd.Divsteps.bbit
    by_cases h : 0≤st.z ∧ st.g%2=1
    · simp [h,hf]
    · simp [h]
  have back := activeStep_roundtrip q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry
    hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 hr hcontrols hfs st hf v
    (m.drop (measurementCount p)) n
    ((keep u (by simp)).trans hu) ((keep k (by simp)).trans hk)
    ((keep active (by simp)).trans halive) hq hc
    ((signed f (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw)))))))).trans ha)
    ((signed (glow::(gmid++[gsign])) (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw))))))).trans hb)
    ((signed (vlow::(vmid++[vsign])) (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ hw)))))).trans hx)
    ((signed gv (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hw))))).trans hy)
    hlo1 hhi1 hlo2 hhi2 hlo3 hhi3 hcn hzero hcarry hcounter
    ((regs zero (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw)))))))))).trans hz0)
    ((regs carry (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw)))))))))).trans hcarry0)
  rw [taggedStep,taggedStepInverse,run_append,run_take,run_append,run_take,back]
  exact run_reverse_proper _ (branchTags_proper _ _ _ _ htn) s m _

private theorem state_eq (a b : State) (hp : a.phase=b.phase)
    (hb : ∀ w,a.basis w=b.basis w) : a=b := by
  have hh := funext hb
  cases a; cases b; simp_all

theorem taggedStepInverse_idle (q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire)
    (hn1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).Nodup)
    (hn2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).Nodup)
    (hgn : (glow::(gmid++[gsign])).Nodup)
    (hvn : (active::vlow::(vmid++[vsign])).Nodup)
    (hl1 : f.length=gmid.length+2) (hl2 : gv.length=vmid.length+2)
    (hr : (q::((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv))).Nodup)
    (htn : [zsign,glow,parity,q].Nodup)
    (hcn : (active::q::(zero++z++carry)).Nodup)
    (hzero : zero.length=z.length) (hcarry : carry.length+1=z.length)
    (s : State) (m : List Bool) (hu : s.basis u=false) (hk : s.basis k=false)
    (hc : s.basis parity=false) (ha : s.basis active=false) (hg : signedRegValue (glow::(gmid++[gsign])) s.basis=0)
    (hq : s.basis q=false) (hz0 : regValue zero s.basis=0) (hcarry0 : regValue carry s.basis=0) :
    run (taggedStepInverse q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s=s := by
  have hglow : s.basis glow=false := (signedRegValue_even_iff glow (gmid++[gsign]) s.basis).mp (by rw [hg]; rfl)
  have hs : s.basis gsign=false := by
    by_contra h
    have hh := (signedRegValue_neg_iff (glow::gmid) gsign s.basis).mpr (Bool.eq_true_of_not_eq_false h)
    simp only [List.cons_append] at hh
    rw [hg] at hh
    omega
  have ht : run (branchTags zsign glow parity q) m s=s := by
    rw [branchTags_correct zsign glow parity q htn s m hc hq]
    apply state_eq
    · rfl
    · intro w
      by_cases hwq : w=q
      · subst w; simp [writeBit,hglow,hq]
      by_cases hwp : w=parity
      · subst w; simp [writeBit,hglow,hc,hwq]
      simp [writeBit,hwq,hwp]
  rw [taggedStepInverse,run_append,run_take,
    activeStepInverse_idle q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry
      hn1 hn2 hgn hvn hl1 hl2 hr hcn hzero hcarry s m hu hk hc ha hs hq hz0 hcarry0]
  have back := run_reverse_proper _ (branchTags_proper _ _ _ _ htn) s m
    (m.drop (measurementCount (activeStepInverse q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry)))
  rwa [ht] at back

end ECDSAAdd.Arithmetic.Paper935
