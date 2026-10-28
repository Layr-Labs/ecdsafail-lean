import ECDSAAdd.Arithmetic.Paper935.RoutedInverse
import ECDSAAdd.Arithmetic.Paper935.IdleRows
import ECDSAAdd.Arithmetic.Divsteps.CounterUpdateInverse

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

def activeStepInverse (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) : Program :=
  counterUpdateInverse active q zero z carry ++
    routedStageInverse q parity u k active glow gsign vlow vsign f gmid vmid gv

theorem activeStep_roundtrip (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv zero z carry : List Wire)
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
    (st : ECDSAAdd.Divsteps.ZState) (hf : st.f%2=1) (s : State) (m n : List Bool)
    (hu : s.basis u=false) (hk : s.basis k=false) (halive : s.basis active=true)
    (hq : s.basis q=decide (0≤st.z ∧ st.g%2=1))
    (hc : s.basis parity=decide (ECDSAAdd.Divsteps.bbit st=1))
    (ha : signedRegValue f s.basis=st.f)
    (hb : signedRegValue (glow::(gmid++[gsign])) s.basis=st.g)
    (hx : signedRegValue (vlow::(vmid++[vsign])) s.basis=st.fv)
    (hy : signedRegValue gv s.basis=st.gv)
    (hlo1 : -((2^(gmid.length+1):Nat):Int)≤2*(ECDSAAdd.Divsteps.zStep st).g)
    (hhi1 : 2*(ECDSAAdd.Divsteps.zStep st).g<((2^(gmid.length+1):Nat):Int))
    (hlo2 : -((2^(gv.length-1):Nat):Int)≤(ECDSAAdd.Divsteps.zStep st).gv)
    (hhi2 : (ECDSAAdd.Divsteps.zStep st).gv<((2^(gv.length-1):Nat):Int))
    (hlo3 : -((2^(vmid.length+1):Nat):Int)≤(ECDSAAdd.Divsteps.zStep st).fv)
    (hhi3 : (ECDSAAdd.Divsteps.zStep st).fv<((2^(vmid.length+1):Nat):Int))
    (hcn : (active::q::(zero++z++carry)).Nodup)
    (hzero : zero.length=z.length) (hcarry : carry.length+1=z.length)
    (hcounter : List.Disjoint (active::q::(zero++z++carry))
      (f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv))
    (hz0 : regValue zero s.basis=0) (hcarry0 : regValue carry s.basis=0) :
    run (activeStepInverse q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry) n
      (run (activeStep q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry) m s)=s := by
  let r := routedStage q parity u k active glow gsign vlow vsign f gmid vmid gv
  let v := run r m s
  have hr0 := routedStage_divstep q parity u k active glow gsign vlow vsign f gmid vmid gv
    hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 hr hcontrols hfs st hf s m hu hk halive hq hc ha hb hx hy
    hlo1 hhi1 hlo2 hhi2 hlo3 hhi3
  have keep (w : Wire) (hw : w∈active::q::(zero++z++carry)) : v.basis w=s.basis w :=
    hr0.2.1 w (List.disjoint_left.mp hcounter hw)
  have vz0 : regValue zero v.basis=0 :=
    (regValue_congr _ _ _ (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append]; tauto))).trans hz0
  have vc0 : regValue carry v.basis=0 :=
    (regValue_congr _ _ _ (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append]; tauto))).trans hcarry0
  have back := counterUpdateInverse_after_forward active q zero z carry hcn hzero hcarry
    v (m.drop (measurementCount r)) n
    (fun _ => (keep active (by simp)).trans halive) vz0 vc0
  rw [activeStep,activeStepInverse,run_append,run_take,run_append,run_take]
  rw [back]
  exact routedStage_roundtrip q parity u k active glow gsign vlow vsign f gmid vmid gv
    hn1 hn2 hgn hvn hl1 hl2 hr s m _ hu hk

theorem activeStepInverse_idle (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv zero z carry : List Wire)
    (hn1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).Nodup)
    (hn2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).Nodup)
    (hgn : (glow::(gmid++[gsign])).Nodup)
    (hvn : (active::vlow::(vmid++[vsign])).Nodup)
    (hl1 : f.length=gmid.length+2) (hl2 : gv.length=vmid.length+2)
    (hr : (q::((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv))).Nodup)
    (hcn : (active::q::(zero++z++carry)).Nodup)
    (hzero : zero.length=z.length) (hcarry : carry.length+1=z.length)
    (s : State) (m : List Bool) (hu : s.basis u=false) (hk : s.basis k=false)
    (hc : s.basis parity=false) (ha : s.basis active=false) (hs : s.basis gsign=false)
    (hq : s.basis q=false) (hz0 : regValue zero s.basis=0) (hcarry0 : regValue carry s.basis=0) :
    run (activeStepInverse q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry) m s=s := by
  have hrow (ms : List Bool) := rowStage_idle q parity u k active glow gsign vlow vsign
    f gmid vmid gv hn1 hn2 hvn hl1 hl2 s ms hu hk hc ha hs
  have hroute := routeRows_idle q f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv
    (by simpa using hl1) (by simpa using hl2.symm) hr s [] hq
  have hf : run (routedStage q parity u k active glow gsign vlow vsign f gmid vmid gv) [] s=s := by
    rw [routedStage,run_append,run_take,hroute,hrow]
  rw [activeStepInverse,run_append,run_take,
    counterUpdateInverse_frozen active q zero z carry hcn hzero hcarry s m ha hq hz0 hcarry0]
  have back := routedStage_roundtrip q parity u k active glow gsign vlow vsign f gmid vmid gv
    hn1 hn2 hgn hvn hl1 hl2 hr s []
    (m.drop (measurementCount (counterUpdateInverse active q zero z carry))) hu hk
  rwa [hf] at back

end ECDSAAdd.Arithmetic.Paper935
