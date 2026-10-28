import ECDSAAdd.Arithmetic.Paper935.SlotBody
import ECDSAAdd.Arithmetic.Divsteps.SwapHistory

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

/-- Retire the swap tag from the updated coefficient bit before old activity
is cleared by the freeze post-stage. The measurement includes its CZ correction. -/
def retiredBody (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) : Program :=
  slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry ++
    eraseAnd active (StepRow.mk vlow vmid vsign).second q

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

private theorem retire_row_subset (u k active : Wire) (zero carry z f g fv gv : List Wire) :
    f++g++fv++gv++z ⊆ u::k::active::(zero++carry++z++f++g++fv++gv) := by
  intro w hw
  simp only [List.mem_cons,List.mem_append] at hw ⊢
  tauto

theorem retiredBody_run (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
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
    (p : Int) (hinv : ECDSAAdd.Divsteps.Inv p st) (hodd : p%2=1) :
    let v := run (slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s
    run (retiredBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s=
      ⟨v.phase,writeBit v.basis q false⟩ := by
  have hb := slotBody_controls frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry zlo hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 hr hcontrols hfs hcn hzero hcarry hwidth hcounter hzview htn htsep hakeep hfreeze st hf s m hz0 hcarry0 hzval hzlo hzhi hu hk hacle hq0 hp0 ha hb hx hy hlo1 hhi1 hlo2 hhi2 hlo3 hhi3 hfgzero
  let v := run (slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s
  have hw := swap_witness p st hinv hodd (s.basis frozen) active q
    (StepRow.mk vlow vmid vsign) v hb.2.2.1 hb.1.1 hb.2.2.2.2.2.2.2.2.1 hfgzero
  have haq : active≠q := fun he => (List.nodup_cons.mp hcn).1 (by simp [he])
  have hqrow : q∉(vlow::(vmid++[vsign])) := by
    intro hmem
    exact List.disjoint_left.mp hcontrols (by simp)
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hmem)))
  have hsq : (StepRow.mk vlow vmid vsign).second≠q := by
    intro he
    exact hqrow (he ▸ (StepRow.mk vlow vmid vsign).second_mem)
  dsimp only
  rw [retiredBody,run_append,run_take]
  exact eraseAnd_run active _ q haq hsq v _ hw

theorem retiredBody_spec (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
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
    (p : Int) (hinv : ECDSAAdd.Divsteps.Inv p st) (hodd : p%2=1) :
    let t := run (retiredBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s
    t.phase=s.phase ∧ t.basis active= !s.basis frozen ∧ t.basis frozen=s.basis frozen ∧
      (∀ w,w∉active::q::parity::(f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z) → t.basis w=s.basis w) ∧
      signedRegValue z t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).z ∧
      signedRegValue f t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).f ∧
      signedRegValue (skywalkHalfView glow (gmid++[gsign])) t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).g ∧
      signedRegValue (vlow::(vmid++[vsign])) t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).fv ∧
      signedRegValue gv t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).gv := by
  have hspec := slotBody_spec frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry zlo hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 hr hcontrols hfs hcn hzero hcarry hwidth hcounter hzview htn htsep hakeep hfreeze st hf s m hz0 hcarry0 hzval hzlo hzhi hu hk hacle hq0 hp0 ha hb hx hy hlo1 hhi1 hlo2 hhi2 hlo3 hhi3 hfgzero
  have he := retiredBody_run frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry zlo hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 hr hcontrols hfs hcn hzero hcarry hwidth hcounter hzview htn htsep hakeep hfreeze st hf s m hz0 hcarry0 hzval hzlo hzhi hu hk hacle hq0 hp0 ha hb hx hy hlo1 hhi1 hlo2 hhi2 hlo3 hhi3 hfgzero p hinv hodd
  let v := run (slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s
  have haq : active≠q := fun hh => hakeep (by simp [hh])
  have hfq : frozen≠q := fun hh => hfreeze (by simp [hh])
  have nq : q∉f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z :=
    fun hm => List.disjoint_left.mp htsep (by simp)
      (retire_row_subset u k active zero carry z f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv hm)
  have signed (xs : List Wire) (hx : xs ⊆ f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z) :
      signedRegValue xs (writeBit v.basis q false)=signedRegValue xs v.basis := by
    unfold signedRegValue
    rw [regValue_congr xs _ v.basis (by
      intro w hw
      exact Function.update_of_ne (fun (hh : w=q) => nq (hh ▸ hx hw)) _ _)]
  dsimp only
  rw [he]
  refine ⟨hspec.1,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [writeBit,Function.update_of_ne haq] using hspec.2.1
  · simpa only [writeBit,Function.update_of_ne hfq] using hspec.2.2.1
  · intro w hw
    have hwq : w≠q := fun hh => hw (by simp [hh])
    exact (Function.update_of_ne hwq _ _).trans (hspec.2.2.2.1 w hw)
  · exact (signed z (by intro w hw; exact List.mem_append_right _ hw)).trans hspec.2.2.2.2.1
  · exact (signed f (by intro w hw; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw))))).trans hspec.2.2.2.2.2.1
  · have hv : skywalkHalfView glow (gmid++[gsign]) ⊆ glow::(gmid++[gsign]) := by
      intro w hw
      simpa [skywalkHalfView,List.mem_append,or_comm,or_left_comm,or_assoc] using hw
    exact (signed _ (by intro w hw; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hv hw)))))).trans hspec.2.2.2.2.2.2.1
  · exact (signed _ (by intro w hw; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw)))).trans hspec.2.2.2.2.2.2.2.1
  · exact (signed gv (by intro w hw; exact List.mem_append_left _ (List.mem_append_right _ hw))).trans hspec.2.2.2.2.2.2.2.2

theorem retiredBody_counts (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) :
    toffoliCount (retiredBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry)=
      toffoliCount (taggedStep q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) ∧
    measurementCount (retiredBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry)=
      measurementCount (taggedStep q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry)+1 := by
  have h := slotBody_counts frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry
  simp [retiredBody,toffoliCount_append,measurementCount_append,eraseAnd,toffoliCount,measurementCount,h.1,h.2]

theorem retiredBody_support (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) :
    wires (retiredBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry)=
      wires (slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) ∪
        {q,active,(StepRow.mk vlow vmid vsign).second} := by
  simp [retiredBody,wires_append,eraseAnd,wires,Instr.wires,correctionWires,Finset.insert_comm]

end ECDSAAdd.Arithmetic.Paper935
