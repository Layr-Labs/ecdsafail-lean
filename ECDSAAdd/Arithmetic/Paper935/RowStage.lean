import ECDSAAdd.Arithmetic.Paper935.BranchRow
import ECDSAAdd.Arithmetic.Divsteps.SignedDouble

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

private theorem signed_eq (xs : List Wire) (s t : BasisState)
    (h : ∀ w∈xs,s w=t w) : signedRegValue xs s=signedRegValue xs t := by
  unfold signedRegValue
  rw [regValue_congr xs s t h]

/-- Finish the row update by doubling fv on active lanes and halving even g.
The half is read in its rotated view, so this program allocates no scratch. -/
def finishRows (active glow gsign vlow vsign : Wire) (vmid : List Wire) : Program :=
  doubleSigned active vlow vsign vmid ++ skywalkSignedHalf gsign glow

theorem finishRows_run (active glow gsign vlow vsign : Wire)
    (gmid vmid gv : List Wire)
    (hgn : (glow::(gmid++[gsign])).Nodup)
    (hvn : (active::vlow::(vmid++[vsign])).Nodup)
    (hgv : List.Disjoint (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])))
    (hyv : List.Disjoint gv (vlow::(vmid++[vsign])))
    (hyg : glow∉gv) (s : State) (m : List Bool)
    (heven : signedRegValue (glow::(gmid++[gsign])) s.basis%2=0)
    (hfit : s.basis active=true →
      -((2^(vmid.length+1):Nat):Int)≤2*signedRegValue (vlow::(vmid++[vsign])) s.basis ∧
      2*signedRegValue (vlow::(vmid++[vsign])) s.basis<((2^(vmid.length+1):Nat):Int)) :
    let t := run (finishRows active glow gsign vlow vsign vmid) m s
    t.phase=s.phase ∧
      (∀ w,w∉(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign])) → t.basis w=s.basis w) ∧
      signedRegValue (skywalkHalfView glow (gmid++[gsign])) t.basis=
        signedRegValue (glow::(gmid++[gsign])) s.basis/2 ∧
      signedRegValue (vlow::(vmid++[vsign])) t.basis=
        (if s.basis active then 2*signedRegValue (vlow::(vmid++[vsign])) s.basis
         else signedRegValue (vlow::(vmid++[vsign])) s.basis) ∧
      signedRegValue gv t.basis=signedRegValue gv s.basis := by
  let v := run (doubleSigned active vlow vsign vmid) m s
  have hv := doubleSigned_correct active vlow vsign vmid hvn s m hfit
  have hg : signedRegValue (glow::(gmid++[gsign])) v.basis =
      signedRegValue (glow::(gmid++[gsign])) s.basis :=
    signed_eq _ _ _ (fun w hw => hv.2.1 w (List.disjoint_left.mp hgv hw))
  have hy : signedRegValue gv v.basis=signedRegValue gv s.basis :=
    signed_eq _ _ _ (fun w hw => hv.2.1 w (List.disjoint_left.mp hyv hw))
  have hsl : gsign≠glow := by
    intro h
    exact (List.nodup_cons.mp hgn).1 (by simp [←h])
  have hh := skywalkSignedHalf_int glow gsign gmid hsl (List.nodup_cons.mp hgn).1 v m
    (by rwa [hg])
  have hf := skywalkSignedHalf_frame gsign glow v m
  have hvl : glow∉vlow::(vmid++[vsign]) := List.disjoint_left.mp hgv (by simp)
  dsimp only
  rw [finishRows,run_append,run_take]
  simp only [(doubleSigned_counts active vlow vsign vmid).2,List.drop_zero]
  refine ⟨hf.1.trans hv.1,?_,hh.trans (congrArg (fun x : Int => x/2) hg),?_,?_⟩
  · intro w hw
    have hwl : w≠glow := fun h => hw (by simp [h])
    have hwv : w∉vlow::(vmid++[vsign]) := fun h => hw (List.mem_append_right _ h)
    exact (hf.2 w hwl).trans (hv.2.1 w hwv)
  · exact (signed_eq _ _ _ (fun w hw => hf.2 w (fun h => hvl (h ▸ hw)))).trans hv.2.2
  · exact (signed_eq _ _ _ (fun w hw => hf.2 w (fun h => hyg (h ▸ hw)))).trans hy

def rowStage (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire) : Program :=
  branchPair q parity u k f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv ++
    finishRows active glow gsign vlow vsign vmid

theorem rowStage_divstep (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire)
    (hn1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).Nodup)
    (hn2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).Nodup)
    (hgn : (glow::(gmid++[gsign])).Nodup)
    (hvn : (active::vlow::(vmid++[vsign])).Nodup)
    (hsep : List.Disjoint (glow::(gmid++[gsign])) ((vlow::(vmid++[vsign]))++gv))
    (hvs : List.Disjoint (vlow::(vmid++[vsign])) ((glow::(gmid++[gsign]))++gv))
    (hac : active∉(glow::(gmid++[gsign]))++gv)
    (hl1 : f.length=gmid.length+2) (hl2 : gv.length=vmid.length+2)
    (st : ECDSAAdd.Divsteps.ZState) (hf : st.f%2=1) (s : State) (m : List Bool)
    (hu : s.basis u=false) (hk : s.basis k=false) (halive : s.basis active=true)
    (hq : s.basis q=decide (0≤st.z ∧ st.g%2=1))
    (hc : s.basis parity=decide (ECDSAAdd.Divsteps.bbit st=1))
    (ha : signedRegValue f s.basis=if 0≤st.z ∧ st.g%2=1 then st.g else st.f)
    (hb : signedRegValue (glow::(gmid++[gsign])) s.basis=
      if 0≤st.z ∧ st.g%2=1 then st.f else st.g)
    (hx : signedRegValue (vlow::(vmid++[vsign])) s.basis=
      if 0≤st.z ∧ st.g%2=1 then st.gv else st.fv)
    (hy : signedRegValue gv s.basis=if 0≤st.z ∧ st.g%2=1 then st.fv else st.gv)
    (hlo1 : -((2^(gmid.length+1):Nat):Int)≤2*(ECDSAAdd.Divsteps.zStep st).g)
    (hhi1 : 2*(ECDSAAdd.Divsteps.zStep st).g<((2^(gmid.length+1):Nat):Int))
    (hlo2 : -((2^(gv.length-1):Nat):Int)≤(ECDSAAdd.Divsteps.zStep st).gv)
    (hhi2 : (ECDSAAdd.Divsteps.zStep st).gv<((2^(gv.length-1):Nat):Int))
    (hlo3 : -((2^(vmid.length+1):Nat):Int)≤(ECDSAAdd.Divsteps.zStep st).fv)
    (hhi3 : (ECDSAAdd.Divsteps.zStep st).fv<((2^(vmid.length+1):Nat):Int)) :
    let t := run (rowStage q parity u k active glow gsign vlow vsign f gmid vmid gv) m s
    t.phase=s.phase ∧
      (∀ w,w∉(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign]))++gv → t.basis w=s.basis w) ∧
      signedRegValue (skywalkHalfView glow (gmid++[gsign])) t.basis=(ECDSAAdd.Divsteps.zStep st).g ∧
      signedRegValue (vlow::(vmid++[vsign])) t.basis=(ECDSAAdd.Divsteps.zStep st).fv ∧
      signedRegValue gv t.basis=(ECDSAAdd.Divsteps.zStep st).gv := by
  let p := branchPair q parity u k f (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) gv
  let v := run p m s
  have hp := branchPair_divstep q parity u k f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv hn1 hn2 hsep (by simpa using hl1)
    (by simpa using hl2.symm) (by simp) (by omega)
    st hf s m hu hk hq hc ha hb hx hy (by simpa using hlo1) (by simpa using hhi1) hlo2 hhi2
  have va : v.basis active=true := (hp.2.1 active hac).trans halive
  have vx : signedRegValue (vlow::(vmid++[vsign])) v.basis =
      signedRegValue (vlow::(vmid++[vsign])) s.basis :=
    signed_eq _ _ _ (fun w hw => hp.2.1 w (List.disjoint_left.mp hvs hw))
  have hdouble : 2*signedRegValue (vlow::(vmid++[vsign])) v.basis =
      (ECDSAAdd.Divsteps.zStep st).fv := by
    rw [vx,hx]
    unfold ECDSAAdd.Divsteps.zStep
    split_ifs <;> rfl
  have hgv : List.Disjoint (glow::(gmid++[gsign])) (vlow::(vmid++[vsign])) :=
    List.disjoint_left.mpr (fun w hw hv => List.disjoint_left.mp hsep hw (List.mem_append_left _ hv))
  have hyv : List.Disjoint gv (vlow::(vmid++[vsign])) :=
    List.disjoint_left.mpr (fun w hw hv => List.disjoint_left.mp hvs hv (List.mem_append_right _ hw))
  have hyg : glow∉gv := fun hw => List.disjoint_left.mp hsep (by simp) (List.mem_append_right _ hw)
  have heven : signedRegValue (glow::(gmid++[gsign])) v.basis%2=0 := by
    rw [hp.2.2.1]; omega
  have ht := finishRows_run active glow gsign vlow vsign gmid vmid gv hgn hvn hgv hyv hyg v
    (m.drop (measurementCount p)) heven (fun _ => by rw [hdouble]; exact ⟨hlo3,hhi3⟩)
  dsimp only
  rw [rowStage,run_append,run_take]
  refine ⟨ht.1.trans hp.1,?_,?_,?_,?_⟩
  · intro w hw
    have h1 : w∉(glow::(gmid++[gsign]))++gv := by
      simp only [List.mem_append] at *; tauto
    have h2 : w∉(glow::(gmid++[gsign]))++(vlow::(vmid++[vsign])) := by
      simp only [List.mem_append] at *; tauto
    exact (ht.2.1 w h2).trans (hp.2.1 w h1)
  · rw [ht.2.2.1,hp.2.2.1]
    omega
  · rw [ht.2.2.2.1]
    simp only [va,ite_true,hdouble]
  · exact ht.2.2.2.2.trans hp.2.2.2

theorem rowStage_counts (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire)
    (hf : f.length=gmid.length+2) (hv : gv.length=vmid.length+2) :
    toffoliCount (rowStage q parity u k active glow gsign vlow vsign f gmid vmid gv)=
      (1+(3*(gmid.length+2)-2))+(1+(3*(vmid.length+2)-2))+(vmid.length+2) ∧
      measurementCount (rowStage q parity u k active glow gsign vlow vsign f gmid vmid gv)=2 := by
  have hc := branchPair_counts q parity u k f (glow::(gmid++[gsign]))
    (vlow::(vmid++[vsign])) gv (by simpa using hf) (by simpa using hv.symm)
  simp only [rowStage,finishRows,toffoliCount_append,measurementCount_append,hc.1,hc.2,
    (doubleSigned_counts active vlow vsign vmid).1,(doubleSigned_counts active vlow vsign vmid).2,
    (skywalkSignedHalf_counts gsign glow).1,(skywalkSignedHalf_counts gsign glow).2]
  simp [hv]

theorem rowStage_in_arena (q parity u k active glow gsign vlow vsign : Wire)
    (f gmid vmid gv : List Wire)
    (h1 : (q::parity::u::k::(f++(glow::(gmid++[gsign])))).toFinset⊆arenaWires)
    (h2 : (q::parity::u::k::((vlow::(vmid++[vsign]))++gv)).toFinset⊆arenaWires)
    (h3 : (active::vlow::(vmid++[vsign])).toFinset⊆arenaWires) :
    wires (rowStage q parity u k active glow gsign vlow vsign f gmid vmid gv)⊆arenaWires := by
  rw [rowStage,wires_append]
  apply Finset.union_subset
  · exact branchPair_in_arena q parity u k f (glow::(gmid++[gsign]))
      (vlow::(vmid++[vsign])) gv h1 h2
  · rw [finishRows,wires_append,doubleSigned_wires,skywalkSignedHalf_wires]
    apply Finset.union_subset h3
    intro w hw
    apply h1
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl <;> simp

/-- The relabelled half uses exactly the original physical wires. -/
theorem rowStage_half_view_set (glow gsign : Wire) (gmid : List Wire) :
    (skywalkHalfView glow (gmid++[gsign])).toFinset=
      (glow::(gmid++[gsign])).toFinset := by
  ext w
  simp [skywalkHalfView]
  tauto

end ECDSAAdd.Arithmetic.Paper935
