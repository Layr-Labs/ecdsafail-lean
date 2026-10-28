import ECDSAAdd.Arithmetic.Divsteps.InverseHalfRow
import ECDSAAdd.Arithmetic.Divsteps.InverseCoefficientPair
import ECDSAAdd.Arithmetic.Divsteps.RowBody

set_option maxHeartbeats 800000

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

def inverseRowBody (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry : List Wire) : Program :=
  inverseCoefficientPair q parity cin active vlow vsign vmid vmask gv vcarry ++
    inverseHalfRow q parity cin glow gsign f gmask gmid gcarry

theorem inverseRowBody_after (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry : List Wire)
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
    (hf : signedRegValue f s.basis=routedF st)
    (hg : signedRegValue (glow::(gmid++[gsign])) s.basis=routedG st)
    (hvf : signedRegValue (vlow::(vmid++[vsign])) s.basis=routedFv st)
    (hvg : signedRegValue gv s.basis=routedGv st)
    (hgm : regValue gmask s.basis=0) (hgk : regValue gcarry s.basis=0)
    (hvm : regValue vmask s.basis=0) (hvk : regValue vcarry s.basis=0) :
    run (inverseRowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) mi
      (run (rowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) mf s)=s := by
  let a := halfRow q parity cin glow gsign f gmask gmid gcarry
  let t := run a mf s
  let rest := mf.drop (measurementCount a)
  obtain ⟨_,haf,_⟩ := integerRow_zStep q parity cin glow gsign f gmask gmid gcarry
    hgnd hgs hgt hgc st pB zB cB hbnd hodd hgfit s mf hq hp hi hf hg hgm hgk
  have keep (w : Wire) (hw : w∈q::parity::cin::active::
      ((vlow::(vmid++[vsign]))++vmask++gv++vcarry)) : t.basis w=s.basis w :=
    haf w (fun hin => List.disjoint_left.mp hsep hin hw)
  have kq := keep q (by simp)
  have kp := keep parity (by simp)
  have ki := keep cin (by simp)
  have kvf : signedRegValue (vlow::(vmid++[vsign])) t.basis=routedFv st := by
    unfold signedRegValue
    rw [regValue_congr _ t.basis s.basis
      (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))]
    exact hvf
  have kvg : signedRegValue gv t.basis=routedGv st := by
    unfold signedRegValue
    rw [regValue_congr _ t.basis s.basis
      (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))]
    exact hvg
  have kvm := regValue_congr vmask t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  have kvk := regValue_congr vcarry t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  have hr := routed_rows_bounds hbnd
  have hvfits := rowValue_fits (swapControl st) (parityControl st) (routedFv st) (routedGv st)
    cB gv.length hr.2.2.1 hr.2.2.2 hvfit
  have hvcap : -((2^(gv.length-1):Nat):Int)≤routedGv st ∧
      routedGv st<((2^(gv.length-1):Nat):Int) := by
    have hh := hr.2.2.2
    constructor <;> omega
  have hpair := inverseCoefficientPair_after q parity cin active vlow vsign vmid vmask gv vcarry
    hvnd hdnd hvs hvt hvc (swapControl st) (parityControl st) (routedFv st) (routedGv st)
    hvcap.1 hvcap.2 hvfits.1.1 hvfits.1.2 hvfits.2.1 hvfits.2.2 t rest mi
    (kq.trans hq) (kp.trans hp) (ki.trans hi) kvf kvg (kvm.trans hvm) (kvk.trans hvk)
  have hgfits := rowValue_fits (swapControl st) (parityControl st) (routedF st) (routedG st)
    pB (gmid.length+2) hr.1 hr.2.1 (by simpa using hgfit)
  have hgcap : -((2^(gmid.length+1):Nat):Int)≤routedG st ∧
      routedG st<((2^(gmid.length+1):Nat):Int) := by
    have hh := hr.2.1
    constructor <;> omega
  simp only [inverseRowBody,rowBody,run_append,run_take]
  rw [hpair]
  exact inverseHalfRow_after q parity cin glow gsign f gmask gmid gcarry hgnd hgs
    (by simpa using hgt) (by simpa using hgc) (swapControl st) (parityControl st)
    (routedF st) (routedG st) (by simpa using hgcap.1) (by simpa using hgcap.2)
    (by simpa using hgfits.1.1) (by simpa using hgfits.1.2)
    (by simpa using hgfits.2.1) (by simpa using hgfits.2.2)
    s mf _ hq hp hi hf hg hgm hgk

theorem inverseRowBody_counts (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry : List Wire)
    (hgs : f.length=gmask.length) (hgt : gmask.length=gmid.length+2)
    (hgc : gcarry.length+1=gmid.length+2)
    (hvs : (vlow::(vmid++[vsign])).length=vmask.length)
    (hvt : vmask.length=gv.length) (hvc : vcarry.length+1=gv.length) :
    toffoliCount (inverseRowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry)=
      (3*(gmid.length+2)-2)+((3*gv.length-2)+(vmid.length+2)) ∧
    measurementCount (inverseRowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry)=
      (3*(gmid.length+2)-2)+(3*gv.length-2) := by
  obtain ⟨hgtf,hgm⟩ := inverseHalfRow_counts q parity cin glow gsign f gmask gmid gcarry hgs hgt hgc
  obtain ⟨hvtf,hvm⟩ := inverseCoefficientPair_counts q parity cin active vlow vsign vmid vmask gv vcarry hvs hvt hvc
  simp only [inverseRowBody,toffoliCount_append,measurementCount_append,hgtf,hgm,hvtf,hvm]
  constructor <;> omega

theorem inverseRowBody_wires_eq (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry : List Wire)
    (hgs : f.length=gmask.length) (hgt : gmask.length=gmid.length+2)
    (hgc : gcarry.length+1=gmid.length+2)
    (hvs : (vlow::(vmid++[vsign])).length=vmask.length)
    (hvt : vmask.length=gv.length) (hvc : vcarry.length+1=gv.length) :
    wires (inverseRowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry)=
      wires (rowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) := by
  rw [inverseRowBody,rowBody,wires_append,wires_append,
    inverseCoefficientPair_wires_eq q parity cin active vlow vsign vmid vmask gv vcarry hvs hvt hvc,
    inverseHalfRow_wires_eq q parity cin glow gsign f gmask gmid gcarry hgs hgt hgc]
  exact Finset.union_comm _ _

end ECDSAAdd.Arithmetic.Divsteps
