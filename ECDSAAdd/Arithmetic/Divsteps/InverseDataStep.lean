import ECDSAAdd.Arithmetic.Divsteps.InverseRoutedBody
import ECDSAAdd.Arithmetic.Divsteps.CounterUpdateInverse
import ECDSAAdd.Arithmetic.Divsteps.DataStep

set_option maxHeartbeats 800000

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

def inverseDataStep (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry cz z cc : List Wire) : Program :=
  counterUpdateInverse active q cz z cc ++
    inverseRoutedBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry

theorem inverseDataStep_after (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry cz z cc : List Wire)
    (hctnd : (active::q::(cz++z++cc)).Nodup)
    (hctz : cz.length=z.length) (hctc : cc.length+1=z.length)
    (hctaway : List.Disjoint (active::q::(cz++z++cc))
      (f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv))
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
    (s : State) (mf mi : List Bool)
    (hq : s.basis q=swapControl st) (hp : s.basis parity=parityControl st)
    (ha : s.basis active=activeControl st) (hi : s.basis cin=false)
    (hf : signedRegValue f s.basis=st.f)
    (hg : signedRegValue (glow::(gmid++[gsign])) s.basis=st.g)
    (hvf : signedRegValue (vlow::(vmid++[vsign])) s.basis=st.fv)
    (hvg : signedRegValue gv s.basis=st.gv)
    (hgm : regValue gmask s.basis=0) (hgk : regValue gcarry s.basis=0)
    (hcz : regValue cz s.basis=0)
    (hcc : regValue cc s.basis=0)
    (hvm : regValue vmask s.basis=0) (hvk : regValue vcarry s.basis=0) :
    run (inverseDataStep q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc) mi
      (run (dataStep q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc) mf s)=s := by
  let a := routedBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry
  let t := run a mf s
  let rest := mf.drop (measurementCount a)
  obtain ⟨_,_,_,_,_,hframe⟩ := routedBody_zSlot q parity cin active glow gsign vlow vsign
    f gmid gmask gcarry vmid vmask gv vcarry hrnd hrfg hrvv hrwork hgnd hvnd hdnd hvd hav
    hsep hfsep hgs hgt hgc hvs hvt hvc st pB zB cB hbnd hodd hgfit hvfit s mf
    hq hp ha hi hf hg hvf hvg hgm hgk hvm hvk
  have keep (w : Wire) (hw : w∈active::q::(cz++z++cc)) : t.basis w=s.basis w :=
    hframe w (List.disjoint_left.mp hctaway hw)
  have ka := keep active (by simp)
  have kq := keep q (by simp)
  have kzero := regValue_congr cz t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  have kcarry := regValue_congr cc t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  have hcounter := counterUpdateInverse_after_forward active q cz z cc hctnd hctz hctc t rest mi
    (by rw [kq,ka,hq,ha]; exact swapControl_active st) (kzero.trans hcz) (kcarry.trans hcc)
  simp only [inverseDataStep,dataStep,run_append,run_take]
  rw [hcounter]
  exact inverseRoutedBody_after q parity cin active glow gsign vlow vsign
    f gmid gmask gcarry vmid vmask gv vcarry hrnd hrfg hrvv hrwork hgnd hvnd hdnd hsep
    hgs hgt hgc hvs hvt hvc st pB zB cB hbnd hodd hgfit hvfit s mf _
    hq hp hi hf hg hvf hvg hgm hgk hvm hvk

end ECDSAAdd.Arithmetic.Divsteps
