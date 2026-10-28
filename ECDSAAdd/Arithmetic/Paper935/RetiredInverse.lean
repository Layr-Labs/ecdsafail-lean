import ECDSAAdd.Arithmetic.Paper935.SlotInverse
import ECDSAAdd.Arithmetic.Paper935.RetiredBody

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

private theorem state_eq {s t : State} (hp : s.phase=t.phase) (hb : s.basis=t.basis) : s=t := by
  cases s; cases t; simp_all

theorem retireAnd_restore (q c u : Wire) (hq : q≠u) (hc : c≠u)
    (s : State) (m n : List Bool) (h : s.basis u=(s.basis q && s.basis c)) :
    run [.CCX q c u] n (run (eraseAnd q c u) m s)=s := by
  rw [eraseAnd_run q c u hq hc s m h]
  apply state_eq
  · rfl
  · funext w
    by_cases hw : w=u
    · subst w; simp [run,writeBit,hq,hc,h]
    · simp [run,writeBit,hw]

private theorem swap_witness (p : Int) (st : ECDSAAdd.Divsteps.ZState)
    (hi : ECDSAAdd.Divsteps.Inv p st) (hp : p%2=1)
    (frozen : Bool) (active q : Wire) (fv : StepRow) (v : State)
    (ha : v.basis active= !frozen)
    (hq : v.basis q=decide (0≤st.z ∧ st.g%2=1))
    (hrow : signedRegValue fv.wires v.basis=(if frozen then st else ECDSAAdd.Divsteps.zStep st).fv)
    (hzero : frozen=true → st.g=0) :
    v.basis q=(v.basis active && v.basis fv.second) := by
  rw [ha,hq,fv.second_bit v.basis,hrow]
  cases hf : frozen with
  | false => simpa using ECDSAAdd.Divsteps.swap_bit_law p st hi hp
  | true => simp [hzero hf]

/-- Remint the retired swap from old activity and updated fv, then undo the
actual body. The branch bit is supplied by the preceding reverse decoder. -/
def retiredBodyInverse (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) : Program :=
  [.CCX active (StepRow.mk vlow vmid vsign).second q] ++
    slotBodyInverse frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry

theorem retiredBody_roundtrip (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
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
    (hwidth : 2≤z.length)
    (hcounter : List.Disjoint (active::q::(zero++z++carry))
      (f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv))
    (hzview : z=zlo++[zsign])
    (htn : [zsign,glow,parity,q].Nodup)
    (htsep : List.Disjoint [q,parity]
      (u::k::active::(zero++carry++z++f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv)))
    (hakeep : active∉q::parity::u::k::(zero++carry++z++f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv))
    (hfreeze : frozen∉active::q::parity::(f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z))
    (st : ECDSAAdd.Divsteps.ZState) (hf : st.f%2=1) (s : State) (m n : List Bool)
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
    (p : Int) (hinv : ECDSAAdd.Divsteps.Inv p st) (hodd : p%2=1) :
    run (retiredBodyInverse frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) n
      (run (retiredBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s)=s := by
  have hbody := slotBody_controls frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry zlo hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 hr hcontrols hfs hcn hzero hcarry hwidth hcounter hzview htn htsep hakeep hfreeze st hf s m hz0 hcarry0 hzval hzlo hzhi hu hk hacle hq0 hp0 ha hb hx hy hlo1 hhi1 hlo2 hhi2 hlo3 hhi3 hfgzero
  let v := run (slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s
  have hw := swap_witness p st hinv hodd (s.basis frozen) active q
    (StepRow.mk vlow vmid vsign) v hbody.2.2.1 hbody.1.1 hbody.2.2.2.2.2.2.2.2.1 hfgzero
  have haq : active≠q := fun he => (List.nodup_cons.mp hcn).1 (by simp [he])
  have hqrow : q∉(vlow::(vmid++[vsign])) := by
    intro hmem
    exact List.disjoint_left.mp hcontrols (by simp)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hmem)))
  have hsq : (StepRow.mk vlow vmid vsign).second≠q := by
    intro he
    exact hqrow (he ▸ (StepRow.mk vlow vmid vsign).second_mem)
  rw [retiredBody,retiredBodyInverse,run_append,run_take,run_append,run_take]
  simp only [measurementCount,List.drop_zero]
  rw [retireAnd_restore active _ q haq hsq v _ n hw]
  exact slotBody_roundtrip frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry zlo
    hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 hr hcontrols hfs hcn hzero hcarry hcounter hzview htn htsep hakeep hfreeze
    st hf s m n hz0 hcarry0 hzval hu hk hacle hq0 hp0 ha hb hx hy
    hlo1 hhi1 hlo2 hhi2 hlo3 hhi3 hfgzero

theorem retiredBodyInverse_counts (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire)
    (hf : f.length=gmid.length+2) (hv : gv.length=vmid.length+2)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length) :
    toffoliCount (retiredBodyInverse frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry)=
      toffoliCount (retiredBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry)+1 ∧
    measurementCount (retiredBodyInverse frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry)+1=
      measurementCount (retiredBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) := by
  have h1 := branchRowInverse_counts q parity u k f (glow::(gmid++[gsign])) (by simpa using hf)
  have h2 := branchRowInverse_counts q parity u k (vlow::(vmid++[vsign])) gv (by simpa using hv.symm)
  have h3 := branchRow_counts q parity u k f (glow::(gmid++[gsign])) (by simpa using hf)
  have h4 := branchRow_counts q parity u k (vlow::(vmid++[vsign])) gv (by simpa using hv.symm)
  have h5 := counterUpdateInverse_counts active q zero z carry hz hc
  have h6 := counterUpdate_counts active q zero z carry hz hc
  simp only [retiredBodyInverse,slotBodyInverse,taggedStepInverse,activeStepInverse,routedStageInverse,
    rowStageInverse,branchPairInverse,retiredBody,slotBody,taggedStep,activeStep,routedStage,rowStage,branchPair,
    toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
    h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,
    mintActivity,branchTags,eraseAnd,toffoliCount,measurementCount]
  constructor <;> omega

end ECDSAAdd.Arithmetic.Paper935
