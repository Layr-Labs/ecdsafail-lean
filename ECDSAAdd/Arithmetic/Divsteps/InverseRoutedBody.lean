import ECDSAAdd.Arithmetic.Divsteps.InverseRowBody
import ECDSAAdd.Arithmetic.Divsteps.InverseRouting
import ECDSAAdd.Arithmetic.Divsteps.RoutedBody

set_option maxHeartbeats 800000

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

def inverseRoutedBody (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry : List Wire) : Program :=
  inverseRowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry ++
    routeRows q f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv

theorem inverseRoutedBody_after (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry : List Wire)
    (hrnd : (q::((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv))).Nodup)
    (hrfg : f.length=(glow::(gmid++[gsign])).length)
    (hrvv : (vlow::(vmid++[vsign])).length=gv.length)
    (hrwork : List.Disjoint (parity::cin::active::(gmask++gcarry++vmask++vcarry))
      ((f++(vlow::(vmid++[vsign])))++((glow::(gmid++[gsign]))++gv)))
    (hgnd : (q::parity::cin::(f++gmask++(glow::(gmid++[gsign]))++gcarry)).Nodup)
    (hvnd : (q::parity::cin::((vlow::(vmid++[vsign]))++vmask++gv++vcarry)).Nodup)
    (hdnd : (active::vlow::(vmid++[vsign])).Nodup)
    (hsep : List.Disjoint (glow::(gmid++[gsign]))
      (q::parity::cin::active::((vlow::(vmid++[vsign]))++vmask++gv++vcarry)))
    (hgs : f.length=gmask.length) (hgt : gmask.length=gmid.length+2)
    (hgc : gcarry.length+1=gmid.length+2)
    (hvs : (vlow::(vmid++[vsign])).length=vmask.length)
    (hvt : vmask.length=gv.length) (hvc : vcarry.length+1=gv.length)
    (st : ZState) (pB zB cB : Int) (hbnd : Bounds pB zB cB st) (hodd : st.f%2=1)
    (hgfit : 2*pB<((2^(gmid.length+1):Nat):Int))
    (hvfit : 2*cB<((2^(gv.length-1):Nat):Int))
    (s : State) (mf mi : List Bool)
    (hq : s.basis q=swapControl st) (hp : s.basis parity=parityControl st)
    (hi : s.basis cin=false)
    (hf : signedRegValue f s.basis=st.f)
    (hg : signedRegValue (glow::(gmid++[gsign])) s.basis=st.g)
    (hvf : signedRegValue (vlow::(vmid++[vsign])) s.basis=st.fv)
    (hvg : signedRegValue gv s.basis=st.gv)
    (hgm : regValue gmask s.basis=0) (hgk : regValue gcarry s.basis=0)
    (hvm : regValue vmask s.basis=0) (hvk : regValue vcarry s.basis=0) :
    run (inverseRoutedBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) mi
      (run (routedBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) mf s)=s := by
  let a := routeRows q f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv
  let t := run a mf s
  let rest := mf.drop (measurementCount a)
  obtain ⟨_,haf,_⟩ := routeRows_correct q f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv hrfg hrvv hrnd s mf
  obtain ⟨hrf,hrg,hrfv,hrgv⟩ := routeRows_signed q f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv hrfg hrvv hrnd s mf
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
  have hbody := inverseRowBody_after q parity cin active glow gsign vlow vsign
    f gmid gmask gcarry vmid vmask gv vcarry hgnd hvnd hdnd hsep
    hgs hgt hgc hvs hvt hvc st pB zB cB hbnd hodd hgfit hvfit t rest mi
    (kq.trans hq) (kp.trans hp) (ki.trans hi)
    hrf hrg hrfv hrgv (kgm.trans hgm) (kgk.trans hgk) (kvm.trans hvm) (kvk.trans hvk)
  simp only [inverseRoutedBody,routedBody,run_append,run_take]
  rw [hbody]
  exact routeRows_after q f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv
    hrfg hrvv hrnd s mf _

end ECDSAAdd.Arithmetic.Divsteps
