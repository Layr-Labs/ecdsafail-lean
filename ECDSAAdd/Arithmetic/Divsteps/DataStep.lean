import ECDSAAdd.Arithmetic.Divsteps.RoutedBody
import ECDSAAdd.Arithmetic.Divsteps.PrepareControls

set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- A full data update with prepared controls: route, update four rows, update
counter. Controls are retained for the enclosing reversible schedule. -/
def dataStep (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry cz z cc : List Wire) : Program :=
  routedBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry ++
    counterUpdate active q cz z cc

private theorem signed_congr (xs : List Wire) (s t : BasisState)
    (h : ∀ w, w∈xs → s w=t w) : signedRegValue xs s=signedRegValue xs t := by
  unfold signedRegValue
  rw [regValue_congr xs s t h]

theorem dataStep_zSlot (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry cz z cc : List Wire)
    (hctnd : (active::q::(cz++z++cc)).Nodup)
    (hctz : cz.length=z.length) (hctc : cc.length+1=z.length) (hctw : 2≤z.length)
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
    (hzfit : zB+1<((2^(z.length-1):Nat):Int))
    (s : State) (m : List Bool)
    (hq : s.basis q=swapControl st) (hp : s.basis parity=parityControl st)
    (ha : s.basis active=activeControl st) (hi : s.basis cin=false)
    (hf : signedRegValue f s.basis=st.f)
    (hg : signedRegValue (glow::(gmid++[gsign])) s.basis=st.g)
    (hvf : signedRegValue (vlow::(vmid++[vsign])) s.basis=st.fv)
    (hvg : signedRegValue gv s.basis=st.gv)
    (hgm : regValue gmask s.basis=0) (hgk : regValue gcarry s.basis=0)
    (hcz : regValue cz s.basis=0) (hzz : signedRegValue z s.basis=st.z)
    (hcc : regValue cc s.basis=0)
    (hvm : regValue vmask s.basis=0) (hvk : regValue vcarry s.basis=0) :
    (run (dataStep q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc) m s).phase=s.phase ∧
    signedRegValue f (run (dataStep q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc) m s).basis=(zSlot st).f ∧
    signedRegValue (skywalkHalfView glow (gmid++[gsign])) (run (dataStep q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc) m s).basis=(zSlot st).g ∧
    signedRegValue (vlow::(vmid++[vsign])) (run (dataStep q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc) m s).basis=(zSlot st).fv ∧
    signedRegValue gv (run (dataStep q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc) m s).basis=(zSlot st).gv ∧
    signedRegValue z (run (dataStep q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc) m s).basis=(zSlot st).z ∧
    (∀ w, w∉f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv++z →
      (run (dataStep q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry cz z cc) m s).basis w=s.basis w) := by
  let a := routedBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry
  let t := run a m s
  let rest := m.drop (measurementCount a)
  obtain ⟨hap,haf,hag,hafv,hagv,hframe⟩ := routedBody_zSlot q parity cin active glow gsign vlow vsign
    f gmid gmask gcarry vmid vmask gv vcarry hrnd hrfg hrvv hrwork hgnd hvnd hdnd hvd hav
    hsep hfsep hgs hgt hgc hvs hvt hvc st pB zB cB hbnd hodd hgfit hvfit s m
    hq hp ha hi hf hg hvf hvg hgm hgk hvm hvk
  have keep (w : Wire) (hw : w∈active::q::(cz++z++cc)) : t.basis w=s.basis w :=
    hframe w (List.disjoint_left.mp hctaway hw)
  have ka := keep active (by simp)
  have kq := keep q (by simp)
  have kz := signed_congr z t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  have kzero := regValue_congr cz t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  have kcarry := regValue_congr cc t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  obtain ⟨hbp,hbf,hbz⟩ := counterUpdate_zSlot active q cz z cc hctnd hctz hctc hctw
    st pB zB cB hbnd hzfit t rest (ka.trans ha) (kq.trans hq) (kzero.trans hcz)
    (kz.trans hzz) (kcarry.trans hcc)
  have away (w : Wire) (hw : w∈f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv) :
      w∉z := by
    intro hz
    have hc : w∈active::q::(cz++z++cc) := by
      simp only [List.mem_cons,List.mem_append]; tauto
    exact List.disjoint_left.mp hctaway hc hw
  have kf := signed_congr f _ t.basis
    (fun w hw => hbf w (away w (by simp only [List.mem_append] at hw ⊢; tauto)))
  have kg := signed_congr (skywalkHalfView glow (gmid++[gsign])) _ t.basis (by
    intro w hw
    apply hbf w
    apply away w
    have hh : w∈glow::(gmid++[gsign]) := by
      simpa [skywalkHalfView,List.mem_append,or_comm,or_left_comm,or_assoc] using hw
    simp only [List.mem_append]; tauto)
  have kfv := signed_congr (vlow::(vmid++[vsign])) _ t.basis
    (fun w hw => hbf w (away w (by simp only [List.mem_append]; tauto)))
  have kgv := signed_congr gv _ t.basis
    (fun w hw => hbf w (away w (by simp only [List.mem_append]; tauto)))
  rw [dataStep,run_append,run_take]
  refine ⟨hbp.trans hap,kf.trans haf,kg.trans hag,kfv.trans hafv,kgv.trans hagv,hbz,?_⟩
  intro w hw
  have hzout : w∉z := by intro h; apply hw; simp only [List.mem_append]; tauto
  have hrout : w∉f++(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv := by
    intro h; apply hw; simp only [List.mem_append] at h ⊢; tauto
  exact (hbf w hzout).trans (hframe w hrout)

end ECDSAAdd.Arithmetic.Divsteps
