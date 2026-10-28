import ECDSAAdd.Arithmetic.Paper935.RoutedStage
import ECDSAAdd.Arithmetic.Divsteps.CounterUpdate

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

def activeStep (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) : Program :=
  routedStage q parity u k active glow gsign vlow vsign f gmid vmid gv ++
    counterUpdate active q zero z carry

theorem activeStep_divstep (q parity u k active glow gsign vlow vsign : Wire)
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
    (hcn : (active::q::(zero++z++carry)).Nodup)
    (hzero : zero.length=z.length) (hcarry : carry.length+1=z.length)
    (hwidth : 2≤z.length)
    (hcounter : List.Disjoint (active::q::(zero++z++carry))
      (f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv))
    (st : ECDSAAdd.Divsteps.ZState) (hf : st.f%2=1) (s : State) (m : List Bool)
    (hz0 : regValue zero s.basis=0) (hcarry0 : regValue carry s.basis=0)
    (hzval : signedRegValue z s.basis=st.z)
    (hzlo : -((2^(z.length-1):Nat):Int)≤(ECDSAAdd.Divsteps.zStep st).z)
    (hzhi : (ECDSAAdd.Divsteps.zStep st).z<((2^(z.length-1):Nat):Int))
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
    (hhi3 : (ECDSAAdd.Divsteps.zStep st).fv<((2^(vmid.length+1):Nat):Int)) :
    let t := run (activeStep q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry) m s
    t.phase=s.phase ∧
      (∀ w,w∉f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z → t.basis w=s.basis w) ∧
      signedRegValue z t.basis=(ECDSAAdd.Divsteps.zStep st).z ∧
      signedRegValue f t.basis=(ECDSAAdd.Divsteps.zStep st).f ∧
      signedRegValue (skywalkHalfView glow (gmid++[gsign])) t.basis=(ECDSAAdd.Divsteps.zStep st).g ∧
      signedRegValue (vlow::(vmid++[vsign])) t.basis=(ECDSAAdd.Divsteps.zStep st).fv ∧
      signedRegValue gv t.basis=(ECDSAAdd.Divsteps.zStep st).gv := by
  let r := routedStage q parity u k active glow gsign vlow vsign f gmid vmid gv
  let v := run r m s
  have hr0 := routedStage_divstep q parity u k active glow gsign vlow vsign f gmid vmid gv
    hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 hr hcontrols hfs st hf s m
    hu hk halive hq hc ha hb hx hy hlo1 hhi1 hlo2 hhi2 hlo3 hhi3
  have keep (w : Wire) (hw : w∈active::q::(zero++z++carry)) : v.basis w=s.basis w :=
    hr0.2.1 w (List.disjoint_left.mp hcounter hw)
  have vz0 : regValue zero v.basis=0 :=
    (regValue_congr _ _ _ (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append]; tauto))).trans hz0
  have vc0 : regValue carry v.basis=0 :=
    (regValue_congr _ _ _ (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append]; tauto))).trans hcarry0
  have vz : signedRegValue z v.basis=st.z := by
    unfold signedRegValue
    rw [regValue_congr z _ _ (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append]; tauto))]
    exact hzval
  have nextz : counterNext true (decide (0≤st.z ∧ st.g%2=1)) st.z=
      (ECDSAAdd.Divsteps.zStep st).z := by
    simp only [counterNext,ite_true,decide_eq_true_eq]
    unfold ECDSAAdd.Divsteps.zStep
    split_ifs <;> rfl
  have ht := counterUpdate_int_spec active q zero z carry hcn hzero hcarry hwidth
    true (decide (0≤st.z ∧ st.g%2=1)) st.z (fun _ => rfl)
    (by rwa [nextz]) (by rwa [nextz]) v (m.drop (measurementCount r))
    ⟨(keep active (by simp)).trans halive,(keep q (by simp)).trans hq,vz0,vz,vc0⟩
  have frame := counterUpdate_frame active q zero z carry hcn hzero hcarry v
    (m.drop (measurementCount r)) vz0 vc0
  have rowkeep (xs : List Wire)
      (hxs : ∀ w∈xs,w∈f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv) :
      signedRegValue xs (run (counterUpdate active q zero z carry)
        (m.drop (measurementCount r)) v).basis=signedRegValue xs v.basis := by
    unfold signedRegValue
    rw [regValue_congr xs _ _ (fun w hw => frame w (fun hz =>
      List.disjoint_left.mp hcounter (by simp only [List.mem_cons,List.mem_append]; tauto) (hxs w hw)))]
  dsimp only
  rw [activeStep,run_append,run_take]
  refine ⟨ht.1.trans hr0.1,?_,ht.2.2.2.2.1.trans nextz,?_,?_,?_,?_⟩
  · intro w hw
    have hz : w∉z := by simp only [List.mem_append] at hw; tauto
    have ho : w∉f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv := by
      simp only [List.mem_append] at hw ⊢; tauto
    exact (frame w hz).trans (hr0.2.1 w ho)
  · exact (rowkeep f (by intro w hw; simp only [List.mem_append]; tauto)).trans hr0.2.2.1
  · refine (rowkeep (skywalkHalfView glow (gmid++[gsign])) ?_).trans hr0.2.2.2.1
    intro w hw
    simp only [skywalkHalfView,List.mem_append,List.mem_cons] at hw ⊢
    tauto
  · exact (rowkeep (vlow::(vmid++[vsign])) (by intro w hw; simp only [List.mem_append]; tauto)).trans hr0.2.2.2.2.1
  · exact (rowkeep gv (by intro w hw; simp only [List.mem_append]; tauto)).trans hr0.2.2.2.2.2

theorem activeStep_counts (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv zero z carry : List Wire)
    (hf : f.length=gmid.length+2) (hv : gv.length=vmid.length+2)
    (hr : (q::((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv))).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length) :
    toffoliCount (activeStep q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry)=
      (f.length+(vmid.length+2)+
       ((1+(3*(gmid.length+2)-2))+(1+(3*(vmid.length+2)-2))+(vmid.length+2)))+(z.length-1) ∧
    measurementCount (activeStep q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry)=
      2+(z.length-1) := by
  have a := routedStage_counts q parity u k active glow gsign vlow vsign f gmid vmid gv hf hv hr
  have b := counterUpdate_counts active q zero z carry hz hc
  simp only [activeStep,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,and_self]

theorem activeStep_in_arena (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv zero z carry : List Wire)
    (hf : f.length=gmid.length+2) (hv : gv.length=vmid.length+2)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (h1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).toFinset⊆arenaWires)
    (h2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).toFinset⊆arenaWires)
    (h3 : (active::vlow::(vmid++[vsign])).toFinset⊆arenaWires)
    (h4 : (active::q::(zero++z++carry)).toFinset⊆arenaWires) :
    wires (activeStep q parity u k active glow gsign vlow vsign f gmid vmid gv zero z carry)⊆arenaWires := by
  rw [activeStep,wires_append]
  exact Finset.union_subset
    (routedStage_in_arena q parity u k active glow gsign vlow vsign f gmid vmid gv hf hv h1 h2 h3)
    ((counterUpdate_wires_subset active q zero z carry hz hc).trans h4)

end ECDSAAdd.Arithmetic.Paper935
