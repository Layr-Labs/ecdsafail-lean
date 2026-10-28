import ECDSAAdd.Arithmetic.Paper935.Activity
import ECDSAAdd.Arithmetic.Paper935.IdleRows

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

private theorem without_cons {w x : Wire} {xs : List Wire} (h : w∉x::xs) : w≠x ∧ w∉xs := by
  simpa only [List.mem_cons,not_or] using h

private theorem body_subset (q parity u k : Wire) (zero carry z f g fv gv : List Wire) :
    q::parity::(f++g++fv++gv++z) ⊆ q::parity::u::k::(zero++carry++z++f++g++fv++gv) := by
  intro w hw
  simp only [List.mem_cons,List.mem_append] at hw ⊢
  tauto

def slotBody (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) : Program :=
  mintActivity frozen active ++
    taggedStep q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry

theorem slotBody_controls (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
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
    (hfgzero : s.basis frozen=true → st.g=0) :
    let t := run (slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s
    (t.basis q=decide (0≤st.z ∧ st.g%2=1) ∧
      t.basis parity=decide (ECDSAAdd.Divsteps.bbit st=1)) ∧
    (t.phase=s.phase ∧ t.basis active= !s.basis frozen ∧ t.basis frozen=s.basis frozen ∧
      (∀ w,w∉active::q::parity::(f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z) → t.basis w=s.basis w) ∧
      signedRegValue z t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).z ∧
      signedRegValue f t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).f ∧
      signedRegValue (skywalkHalfView glow (gmid++[gsign])) t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).g ∧
      signedRegValue (vlow::(vmid++[vsign])) t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).fv ∧
      signedRegValue gv t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).gv) := by
  let v := run (mintActivity frozen active) m s
  have hfa : frozen≠active := (without_cons hfreeze).1
  have hv := mintActivity_run frozen active hfa s m hacle
  have keep (w : Wire) (hw : w≠active) : v.basis w=s.basis w := by
    dsimp only [v]; rw [hv]; simp [writeBit,hw]
  have memkeep (w : Wire)
      (hw : w∈q::parity::u::k::(zero++carry++z++f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv)) :
      v.basis w=s.basis w := keep w (fun h => hakeep (h ▸ hw))
  have regs (xs : List Wire)
      (hxs : ∀ w∈xs,w∈q::parity::u::k::(zero++carry++z++f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv)) :
      regValue xs v.basis=regValue xs s.basis := regValue_congr xs _ _ (fun w hw => memkeep w (hxs w hw))
  have signed (xs : List Wire)
      (hxs : ∀ w∈xs,w∈q::parity::u::k::(zero++carry++z++f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv)) :
      signedRegValue xs v.basis=signedRegValue xs s.basis := by unfold signedRegValue; rw [regs xs hxs]
  have va : v.basis active= !s.basis frozen := by dsimp only [v]; rw [hv]; simp [writeBit]
  have vp : v.phase=s.phase := by dsimp only [v]; rw [hv]
  have vf : v.basis frozen=s.basis frozen := keep frozen hfa
  have vu : v.basis u=false := (memkeep u (by simp)).trans hu
  have vk : v.basis k=false := (memkeep k (by simp)).trans hk
  have vq : v.basis q=false := (memkeep q (by simp)).trans hq0
  have vc : v.basis parity=false := (memkeep parity (by simp)).trans hp0
  have vz0 : regValue zero v.basis=0 :=
    (regs zero (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw))))))))))).trans hz0
  have vcarry : regValue carry v.basis=0 :=
    (regs carry (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw))))))))))).trans hcarry0
  have vz : signedRegValue z v.basis=st.z :=
    (signed z (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw)))))))))).trans hzval
  have vfv : signedRegValue f v.basis=st.f :=
    (signed f (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw))))))))).trans ha
  have vg : signedRegValue (glow::(gmid++[gsign])) v.basis=st.g :=
    (signed (glow::(gmid++[gsign])) (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw)))))))).trans hb
  have vx : signedRegValue (vlow::(vmid++[vsign])) v.basis=st.fv :=
    (signed (vlow::(vmid++[vsign])) (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ hw))))))).trans hx
  have vy : signedRegValue gv v.basis=st.gv :=
    (signed gv (by intro w hw; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hw)))))).trans hy
  have han : active∉q::parity::(f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z) := by
    intro hw
    exact hakeep (body_subset q parity u k zero carry z f (glow::(gmid++[gsign]))
      (vlow::(vmid++[vsign])) gv hw)
  have hfn := (without_cons hfreeze).2
  dsimp only
  rw [slotBody,run_append,run_take]
  have hm : measurementCount (mintActivity frozen active)=0 := rfl
  simp only [hm,List.drop_zero]
  cases hs : s.basis frozen with
  | false =>
    have hfull := taggedStep_divstep_controls q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry zlo
      hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 hr hcontrols hfs hcn hzero hcarry hwidth hcounter hzview htn htsep
      st hf v m vz0 vcarry vz (hzlo hs) (hzhi hs) vu vk (by simpa only [hs,Bool.not_false] using va)
      vq vc vfv vg vx vy (hlo1 hs) (hhi1 hs) (hlo2 hs) (hhi2 hs) (hlo3 hs) (hhi3 hs)
    refine ⟨hfull.1,?_⟩
    have ht := hfull.2
    simp only [Bool.not_false,Bool.false_eq_true,ite_false]
    refine ⟨ht.1.trans vp,(ht.2.1 active han).trans (by simpa only [hs,Bool.not_false] using va),
      (ht.2.1 frozen hfn).trans (vf.trans hs),?_,ht.2.2⟩
    intro w hw
    have hwa : w≠active := (without_cons hw).1
    exact (ht.2.1 w (without_cons hw).2).trans (keep w hwa)
  | true =>
    have vg0 : signedRegValue (glow::(gmid++[gsign])) v.basis=0 := vg.trans (hfgzero hs)
    have ht := taggedStep_idle q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry
      hn1 hn2 hvn hl1 hl2 hr htn hcn hzero hcarry v m vu vk vc
      (by simpa only [hs,Bool.not_true] using va) vg0 vq vz0 vcarry
    rw [ht]
    refine ⟨?_,?_⟩
    · constructor
      · simpa only [hfgzero hs,Int.zero_emod,Int.reduceEq,and_false,decide_false] using vq
      · simpa [ECDSAAdd.Divsteps.bbit,hfgzero hs] using vc
    simp only [Bool.not_true,ite_true]
    refine ⟨vp,(by simpa only [hs,Bool.not_true] using va),vf.trans hs,?_,vz,vfv,?_,vx,vy⟩
    · intro w hw
      exact keep w (without_cons hw).1
    · exact (halfView_zero glow gsign gmid v.basis vg0).trans (hfgzero hs).symm

theorem slotBody_spec (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
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
    (hfgzero : s.basis frozen=true → st.g=0) :
    let t := run (slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s
    t.phase=s.phase ∧ t.basis active= !s.basis frozen ∧ t.basis frozen=s.basis frozen ∧
      (∀ w,w∉active::q::parity::(f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z) → t.basis w=s.basis w) ∧
      signedRegValue z t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).z ∧
      signedRegValue f t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).f ∧
      signedRegValue (skywalkHalfView glow (gmid++[gsign])) t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).g ∧
      signedRegValue (vlow::(vmid++[vsign])) t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).fv ∧
      signedRegValue gv t.basis=(if s.basis frozen then st else ECDSAAdd.Divsteps.zStep st).gv := by
  exact (slotBody_controls frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry zlo hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 hr hcontrols hfs hcn hzero hcarry hwidth hcounter hzview htn htsep hakeep hfreeze st hf s m hz0 hcarry0 hzval hzlo hzhi hu hk hacle hq0 hp0 ha hb hx hy hlo1 hhi1 hlo2 hhi2 hlo3 hhi3 hfgzero).2

theorem slotBody_counts (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) :
    toffoliCount (slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry)=
      toffoliCount (taggedStep q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) ∧
    measurementCount (slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry)=
      measurementCount (taggedStep q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) := by
  simp only [slotBody,toffoliCount_append,measurementCount_append,
    (activity_counts frozen frozen active).1,(activity_counts frozen frozen active).2.1,Nat.zero_add,and_self]

theorem slotBody_support (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) :
    wires (slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry)=
      [frozen,active].toFinset ∪
        wires (taggedStep q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) := by
  rw [slotBody,wires_append,(activity_wires frozen frozen active).1]

end ECDSAAdd.Arithmetic.Paper935
