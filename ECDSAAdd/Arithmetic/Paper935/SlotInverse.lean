import ECDSAAdd.Arithmetic.Paper935.TaggedInverse
import ECDSAAdd.Arithmetic.Paper935.SlotBody

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

def slotBodyInverse (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
    (f gmid vmid gv zero z carry : List Wire) : Program :=
  taggedStepInverse q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry ++
    (mintActivity frozen active).reverse

theorem slotBody_roundtrip (frozen q parity u k active glow gsign vlow vsign zsign : Wire)
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
    (hakeep : active∉q::parity::u::k::(zero++carry++z++f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv))
    (hfreeze : frozen∉active::q::parity::(f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z))
    (st : ECDSAAdd.Divsteps.ZState) (hf : st.f%2=1) (s : State) (m n : List Bool)
    (hz0 : regValue zero s.basis=0) (hcarry0 : regValue carry s.basis=0)
    (hzval : signedRegValue z s.basis=st.z)
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
    run (slotBodyInverse frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) n
      (run (slotBody frozen q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m s)=s := by
  let v := run (mintActivity frozen active) m s
  have hfa : frozen≠active := by intro h; exact hfreeze (by simp [h])
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
  have back : run (taggedStepInverse q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) n
      (run (taggedStep q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry) m v)=v := by
    cases hs : s.basis frozen with
    | false =>
      exact taggedStep_roundtrip q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry zlo
        hn1 hn2 hgn hvn hsep hvs hac hl1 hl2 hr hcontrols hfs hcn hzero hcarry hcounter hzview htn htsep
        st hf v m n vz0 vcarry vz vu vk (by simpa only [hs,Bool.not_false] using va)
        vq vc vfv vg vx vy (hlo1 hs) (hhi1 hs) (hlo2 hs) (hhi2 hs) (hlo3 hs) (hhi3 hs)
    | true =>
      have vg0 : signedRegValue (glow::(gmid++[gsign])) v.basis=0 := vg.trans (hfgzero hs)
      have idle := taggedStep_idle q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry
        hn1 hn2 hvn hl1 hl2 hr htn hcn hzero hcarry v m vu vk vc
        (by simpa only [hs,Bool.not_true] using va) vg0 vq vz0 vcarry
      rw [idle]
      exact taggedStepInverse_idle q parity u k active glow gsign vlow vsign zsign f gmid vmid gv zero z carry
        hn1 hn2 hgn hvn hl1 hl2 hr htn hcn hzero hcarry v n vu vk vc
        (by simpa only [hs,Bool.not_true] using va) vg0 vq vz0 vcarry
  rw [slotBody,slotBodyInverse,run_append,run_take,run_append,run_take]
  simp only [show measurementCount (mintActivity frozen active)=0 from rfl,List.drop_zero]
  rw [back]
  exact run_reverse_proper _ (by simpa [mintActivity,ProperProgram,ProperGate] using hfa) s m _

end ECDSAAdd.Arithmetic.Paper935
