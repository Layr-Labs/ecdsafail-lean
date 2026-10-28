import ECDSAAdd.Arithmetic.Divsteps.RowBody
import ECDSAAdd.Arithmetic.Divsteps.Routing

set_option maxHeartbeats 800000

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

def routedBody (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry : List Wire) : Program :=
  routeRows q f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv ++
    rowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry

theorem routedBody_zSlot (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry : List Wire)
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
    (s : State) (m : List Bool)
    (hq : s.basis q=swapControl st) (hp : s.basis parity=parityControl st)
    (ha : s.basis active=activeControl st) (hi : s.basis cin=false)
    (hf : signedRegValue f s.basis=st.f)
    (hg : signedRegValue (glow::(gmid++[gsign])) s.basis=st.g)
    (hvf : signedRegValue (vlow::(vmid++[vsign])) s.basis=st.fv)
    (hvg : signedRegValue gv s.basis=st.gv)
    (hgm : regValue gmask s.basis=0) (hgk : regValue gcarry s.basis=0)
    (hvm : regValue vmask s.basis=0) (hvk : regValue vcarry s.basis=0) :
    (run (routedBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) m s).phase=s.phase ∧
    signedRegValue f (run (routedBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) m s).basis=(zSlot st).f ∧
    signedRegValue (skywalkHalfView glow (gmid++[gsign])) (run (routedBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) m s).basis=(zSlot st).g ∧
    signedRegValue (vlow::(vmid++[vsign])) (run (routedBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) m s).basis=(zSlot st).fv ∧
    signedRegValue gv (run (routedBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) m s).basis=(zSlot st).gv ∧
    (∀ w, w∉f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv →
      (run (routedBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) m s).basis w=s.basis w) := by
  let a := routeRows q f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv
  let t := run a m s
  let rest := m.drop (measurementCount a)
  obtain ⟨hap,haf,_⟩ := routeRows_correct q f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv hrfg hrvv hrnd s m
  obtain ⟨hrf,hrg,hrfv,hrgv⟩ := routeRows_signed q f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv hrfg hrvv hrnd s m
  have keep (w : Wire) (hw : w∈parity::cin::active::(gmask++gcarry++vmask++vcarry)) :
      t.basis w=s.basis w := by
    have hout := List.disjoint_left.mp hrwork hw
    exact haf w (fun h => hout (List.mem_append_left _ h))
      (fun h => hout (List.mem_append_right _ h))
  have kq : t.basis q=s.basis q := by
    have h := (List.nodup_cons.mp hrnd).1
    exact haf q (fun hin => h (List.mem_append_left _ hin))
      (fun hin => h (List.mem_append_right _ hin))
  have kp := keep parity (by simp)
  have ki := keep cin (by simp)
  have ka := keep active (by simp)
  have kgm := regValue_congr gmask t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  have kgk := regValue_congr gcarry t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  have kvm := regValue_congr vmask t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  have kvk := regValue_congr vcarry t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  rw [hq,hf,hg] at hrf hrg
  rw [hq,hvf,hvg] at hrfv hrgv
  obtain ⟨hbp,hbf,hbg,hbfv,hbgv,hframe⟩ := rowBody_zSlot q parity cin active glow gsign vlow vsign
    f gmid gmask gcarry vmid vmask gv vcarry hgnd hvnd hdnd hvd hav hsep hfsep
    hgs hgt hgc hvs hvt hvc st pB zB cB hbnd hodd hgfit hvfit t rest
    (kq.trans hq) (kp.trans hp) (ka.trans ha) (ki.trans hi)
    hrf hrg hrfv hrgv (kgm.trans hgm) (kgk.trans hgk) (kvm.trans hvm) (kvk.trans hvk)
  rw [routedBody,run_append,run_take]
  refine ⟨hbp.trans hap,hbf,hbg,hbfv,hbgv,?_⟩
  intro w hw
  have hout : w∉(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv := by
    intro h; apply hw; simp only [List.mem_append] at h ⊢; tauto
  have hleft : w∉f++(vlow::(vmid++[vsign])) := by
    intro h; apply hw; simp only [List.mem_append] at h ⊢; tauto
  have hright : w∉(glow::(gmid++[gsign]))++gv := by
    intro h; apply hw; simp only [List.mem_append] at h ⊢; tauto
  exact (hframe w hout).trans (haf w hleft hright)

end ECDSAAdd.Arithmetic.Divsteps
