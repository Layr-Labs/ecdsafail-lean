import ECDSAAdd.Arithmetic.Divsteps.CoefficientPair

set_option maxHeartbeats 800000

namespace ECDSAAdd.Arithmetic.Divsteps
open ECDSAAdd.Divsteps

/-- Routed integer update followed by both coefficient updates. The two stages
may reuse mask/carry wires, provided the stated clean input contracts hold. -/
def rowBody (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry : List Wire) : Program :=
  halfRow q parity cin glow gsign f gmask gmid gcarry ++
    coefficientPair q parity cin active vlow vsign vmid vmask gv vcarry

private theorem signed_congr (xs : List Wire) (s t : BasisState)
    (h : ∀ w, w∈xs → s w=t w) : signedRegValue xs s=signedRegValue xs t := by
  unfold signedRegValue
  rw [regValue_congr xs s t h]

/-- Both data rows and both coefficient rows are updated by the same physical
program. Halving changes the integer target's wire view. Control preparation,
routing and counter update sit outside this body. -/
theorem rowBody_zSlot (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry : List Wire)
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
    (hf : signedRegValue f s.basis=routedF st)
    (hg : signedRegValue (glow::(gmid++[gsign])) s.basis=routedG st)
    (hvf : signedRegValue (vlow::(vmid++[vsign])) s.basis=routedFv st)
    (hvg : signedRegValue gv s.basis=routedGv st)
    (hgm : regValue gmask s.basis=0) (hgk : regValue gcarry s.basis=0)
    (hvm : regValue vmask s.basis=0) (hvk : regValue vcarry s.basis=0) :
    (run (rowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) m s).phase=s.phase ∧
    signedRegValue f (run (rowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) m s).basis=(zSlot st).f ∧
    signedRegValue (skywalkHalfView glow (gmid++[gsign])) (run (rowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) m s).basis=(zSlot st).g ∧
    signedRegValue (vlow::(vmid++[vsign])) (run (rowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) m s).basis=(zSlot st).fv ∧
    signedRegValue gv (run (rowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) m s).basis=(zSlot st).gv ∧
    (∀ w, w∉(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv →
      (run (rowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry) m s).basis w=s.basis w) := by
  let a := halfRow q parity cin glow gsign f gmask gmid gcarry
  let t := run a m s
  let rest := m.drop (measurementCount a)
  obtain ⟨hap,haf,hag⟩ := integerRow_zStep q parity cin glow gsign f gmask gmid gcarry
    hgnd hgs hgt hgc st pB zB cB hbnd hodd hgfit s m hq hp hi hf hg hgm hgk
  have keep (w : Wire) (hw : w∈q::parity::cin::active::
      ((vlow::(vmid++[vsign]))++vmask++gv++vcarry)) : t.basis w=s.basis w :=
    haf w (fun hin => List.disjoint_left.mp hsep hin hw)
  have kq := keep q (by simp)
  have kp := keep parity (by simp)
  have ki := keep cin (by simp)
  have ka := keep active (by simp)
  have kvf := signed_congr (vlow::(vmid++[vsign])) t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  have kvg := signed_congr gv t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  have kvm := regValue_congr vmask t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  have kvk := regValue_congr vcarry t.basis s.basis
    (fun w hw => keep w (by simp only [List.mem_cons,List.mem_append] at hw ⊢; tauto))
  obtain ⟨hbp,hbf,hbv,hbg⟩ := coefficientPair_zSlot q parity cin active vlow vsign
    vmid vmask gv vcarry hvnd hdnd hvd hav hvs hvt hvc st pB zB cB hbnd hvfit t rest
    (kq.trans hq) (kp.trans hp) (ka.trans ha) (ki.trans hi)
    (kvf.trans hvf) (kvg.trans hvg) (kvm.trans hvm) (kvk.trans hvk)
  have faway (w : Wire) (hw : w∈f) : w∉glow::(gmid++[gsign]) := by
    have hd := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hgnd).2).2).2
    have hc := List.nodup_iff_count.mp hd w
    simp only [List.count_append] at hc
    have hh := List.count_pos_iff.mpr hw
    intro hhg
    have hhg' := List.count_pos_iff.mpr hhg
    omega
  have hbfv := signed_congr f _ t.basis
    (fun w hw => hbf w (List.disjoint_left.mp hfsep hw))
  have hafv := signed_congr f t.basis s.basis (fun w hw => haf w (faway w hw))
  have hgkeep := signed_congr (skywalkHalfView glow (gmid++[gsign])) _ t.basis (by
    intro w hw
    apply hbf w
    have hgin : w∈glow::(gmid++[gsign]) := by
      simpa [skywalkHalfView,List.mem_append,or_comm,or_left_comm,or_assoc] using hw
    intro hvout
    apply List.disjoint_left.mp hsep hgin
    simp only [List.mem_cons,List.mem_append] at hvout ⊢
    tauto)
  rw [rowBody,run_append,run_take]
  refine ⟨hbp.trans hap,hbfv.trans (hafv.trans (hf.trans (target_rows_frozen st).2.2)),
    hgkeep.trans (hag.trans (target_rows_frozen st).1),hbv,hbg,?_⟩
  intro w hw
  have hgout : w∉glow::(gmid++[gsign]) := by
    intro h; apply hw; simp only [List.mem_append]; tauto
  have hvout : w∉(vlow::(vmid++[vsign]))++gv := by
    intro h; apply hw; simp only [List.mem_append] at h ⊢; tauto
  exact (hbf w hvout).trans (haf w hgout)

theorem rowBody_counts (q parity cin active glow gsign vlow vsign : Wire)
    (f gmid gmask gcarry vmid vmask gv vcarry : List Wire)
    (hgs : f.length=gmask.length) (hgt : gmask.length=gmid.length+2)
    (hgc : gcarry.length+1=gmid.length+2)
    (hvs : (vlow::(vmid++[vsign])).length=vmask.length)
    (hvt : vmask.length=gv.length) (hvc : vcarry.length+1=gv.length) :
    toffoliCount (rowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry)=
      (3*(gmid.length+2)-2)+((3*gv.length-2)+(vmid.length+2)) ∧
    measurementCount (rowBody q parity cin active glow gsign vlow vsign f gmid gmask gcarry vmid vmask gv vcarry)=
      (3*(gmid.length+2)-2)+(3*gv.length-2) := by
  obtain ⟨hgtf,hgm⟩ := halfRow_counts q parity cin glow gsign f gmask gmid gcarry hgs hgt hgc
  obtain ⟨hvtf,hvm⟩ := coefficientPair_counts q parity cin active vlow vsign vmid vmask gv vcarry hvs hvt hvc
  simp [rowBody,toffoliCount_append,measurementCount_append,hgtf,hgm,hvtf,hvm]

end ECDSAAdd.Arithmetic.Divsteps
