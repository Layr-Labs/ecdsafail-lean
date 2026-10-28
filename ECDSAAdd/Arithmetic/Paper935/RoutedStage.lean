import ECDSAAdd.Arithmetic.Paper935.RowStage
import ECDSAAdd.Arithmetic.Divsteps.Routing

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

def routedStage (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire) : Program :=
  routeRows q f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv ++
    rowStage q parity u k active glow gsign vlow vsign f gmid vmid gv

theorem routedStage_divstep (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire)
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
    (st : ECDSAAdd.Divsteps.ZState) (hf : st.f%2=1) (s : State) (m : List Bool)
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
    let t := run (routedStage q parity u k active glow gsign vlow vsign f gmid vmid gv) m s
    t.phase=s.phase ∧
      (∀ w,w∉f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv → t.basis w=s.basis w) ∧
      signedRegValue f t.basis=(ECDSAAdd.Divsteps.zStep st).f ∧
      signedRegValue (skywalkHalfView glow (gmid++[gsign])) t.basis=(ECDSAAdd.Divsteps.zStep st).g ∧
      signedRegValue (vlow::(vmid++[vsign])) t.basis=(ECDSAAdd.Divsteps.zStep st).fv ∧
      signedRegValue gv t.basis=(ECDSAAdd.Divsteps.zStep st).gv := by
  let r := routeRows q f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv
  let v := run r m s
  have hr0 := routeRows_correct q f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv (by simpa using hl1) (by simpa using hl2.symm) hr s m
  have hrs := routeRows_signed q f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv (by simpa using hl1) (by simpa using hl2.symm) hr s m
  have ctrl (w : Wire) (hw : w∈[q,parity,u,k,active]) : v.basis w=s.basis w := by
    have hn := List.disjoint_left.mp hcontrols hw
    apply hr0.2.1 w <;> intro hh <;> apply hn
    all_goals simp only [List.mem_append] at hh ⊢; tauto
  have va : signedRegValue f v.basis=if 0≤st.z ∧ st.g%2=1 then st.g else st.f := by
    simpa only [hq,ha,hb,decide_eq_true_eq] using hrs.1
  have vb : signedRegValue (glow::(gmid++[gsign])) v.basis=
      if 0≤st.z ∧ st.g%2=1 then st.f else st.g := by
    simpa only [hq,ha,hb,decide_eq_true_eq] using hrs.2.1
  have vx : signedRegValue (vlow::(vmid++[vsign])) v.basis=
      if 0≤st.z ∧ st.g%2=1 then st.gv else st.fv := by
    simpa only [hq,hx,hy,decide_eq_true_eq] using hrs.2.2.1
  have vy : signedRegValue gv v.basis=if 0≤st.z ∧ st.g%2=1 then st.fv else st.gv := by
    simpa only [hq,hx,hy,decide_eq_true_eq] using hrs.2.2.2
  have ht := rowStage_divstep q parity u k active glow gsign vlow vsign f gmid vmid gv
    hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 st hf v (m.drop (measurementCount r))
    ((ctrl u (by simp)).trans hu) ((ctrl k (by simp)).trans hk)
    ((ctrl active (by simp)).trans halive) ((ctrl q (by simp)).trans hq)
    ((ctrl parity (by simp)).trans hc) va vb vx vy hlo1 hhi1 hlo2 hhi2 hlo3 hhi3
  dsimp only
  rw [routedStage,run_append,run_take]
  refine ⟨ht.1.trans hr0.1,?_,?_,ht.2.2⟩
  · intro w hw
    have ho : w∉(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv := by
      simp only [List.mem_append] at hw ⊢; tauto
    refine (ht.2.1 w ho).trans (hr0.2.1 w ?_ ?_)
    all_goals simp only [List.mem_append] at hw ⊢; tauto
  · have hreg : signedRegValue f
        (run (rowStage q parity u k active glow gsign vlow vsign f gmid vmid gv)
          (m.drop (measurementCount r)) v).basis=signedRegValue f v.basis := by
      unfold signedRegValue
      rw [regValue_congr f _ _ (fun w hw => ht.2.1 w (List.disjoint_left.mp hfs hw))]
    rw [hreg,va]
    unfold ECDSAAdd.Divsteps.zStep
    split_ifs <;> rfl

theorem routedStage_counts (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire)
    (hf : f.length=gmid.length+2) (hv : gv.length=vmid.length+2)
    (hr : (q::((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv))).Nodup) :
    toffoliCount (routedStage q parity u k active glow gsign vlow vsign f gmid vmid gv)=
      f.length+(vmid.length+2)+
      ((1+(3*(gmid.length+2)-2))+(1+(3*(vmid.length+2)-2))+(vmid.length+2)) ∧
    measurementCount (routedStage q parity u k active glow gsign vlow vsign f gmid vmid gv)=2 := by
  have a := routeRows_counts q f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv (by simpa using hf) (by simpa using hv.symm) hr
  have b := rowStage_counts q parity u k active glow gsign vlow vsign f gmid vmid gv hf hv
  simp [routedStage,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]

theorem routedStage_in_arena (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire)
    (hf : f.length=gmid.length+2) (hv : gv.length=vmid.length+2)
    (h1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).toFinset⊆arenaWires)
    (h2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).toFinset⊆arenaWires)
    (h3 : (active::vlow::(vmid++[vsign])).toFinset⊆arenaWires) :
    wires (routedStage q parity u k active glow gsign vlow vsign f gmid vmid gv)⊆arenaWires := by
  rw [routedStage,wires_append]
  apply Finset.union_subset
  · intro w hw
    have hh := swapRegisters_wires q (f++(vlow::(vmid++[vsign])))
      ((glow::(gmid++[gsign]))++gv) (by simp [hf,hv]; omega) hw
    have hm : w∈(q::parity::u::k::(f++(glow::(gmid++[gsign])))).toFinset ∨
        w∈(q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).toFinset := by
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
      tauto
    exact hm.elim (fun h => h1 h) (fun h => h2 h)
  · exact rowStage_in_arena q parity u k active glow gsign vlow vsign f gmid vmid gv h1 h2 h3

end ECDSAAdd.Arithmetic.Paper935
