import ECDSAAdd.Arithmetic.Paper935.WindowRouted
import ECDSAAdd.Arithmetic.Paper935.WindowCounter

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

def RoutedBankLayout.windowStep (L : RoutedBankLayout) (resize : Program)
    (zero z carry : List Wire) : Program :=
  L.program++(resize++counterUpdate L.active L.q zero z carry)

/-- Actual routed arithmetic followed by exit-window shrinkage and the
measured counter update, on both active and frozen lanes. -/
theorem RoutedBankLayout.windowStep_rows (L : RoutedBankLayout) (hv : L.Valid)
    (out : WindowBank) (w : RowWindow) (A C D : Arena) (resize : Program)
    (hp : L.after.Planned out w A C resize) (z zero carry : List Wire)
    (hn : (L.active::L.q::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (hrow : (L.before.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (hown : (L.active::L.q::z).toFinset⊆A.live)
    (hbefore : List.Disjoint (L.active::L.q::z) (L.before.rows.flatMap WindowRow.wires))
    (hafter : List.Disjoint (L.active::L.q::z) (L.after.rows.flatMap WindowRow.wires))
    (hout : List.Disjoint z (out.rows.flatMap WindowRow.wires))
    (hborrow : C.reserve (zero++carry).toFinset=some D)
    (st : ECDSAAdd.Divsteps.ZState) (frozen : Bool) (hf : st.f%2=1)
    (s : State) (m : List Bool) (hu : s.basis L.u=false) (hk : s.basis L.k=false)
    (ha : s.basis L.active= !frozen)
    (hq : s.basis L.q=decide (0≤st.z ∧ st.g%2=1))
    (hb : s.basis L.parity=decide (ECDSAAdd.Divsteps.bbit st=1))
    (he : L.before.Encodes s.basis st) (hzero : frozen=true → st.g=0)
    (hg : frozen=false → PayloadFits (L.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep st).g))
    (hgv : frozen=false → PayloadFits (L.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep st).gv)
    (hfv : frozen=false → PayloadFits (L.vmid.length+1) (ECDSAAdd.Divsteps.zStep st).fv)
    (hready : A.Ready s.basis) (hfit : w.Fits (if frozen then st else ECDSAAdd.Divsteps.zStep st)) :
    let t := run (L.windowStep resize zero z carry) m s
    C.Ready t.basis ∧ out.Encodes t.basis (if frozen then st else ECDSAAdd.Divsteps.zStep st) ∧
    out.Widths w ∧
    regValue z t.basis=counterWord z.length (s.basis L.active) (s.basis L.q) (regValue z s.basis) := by
  let v := run L.program m s
  have r := L.run_pinned hv st frozen hf s m hu hk ha hq hb he hzero hg hgv hfv
  have ready : A.Ready v.basis := by
    intro q hq hn
    rw [r.2.2 q (fun hh => hn (hrow (List.mem_toFinset.mpr hh)))]
    exact hready q hq hn
  have step := L.after.resize_then_counter out w A C D resize hp L.active L.q z zero carry
    hn hz hc hown hafter hout hborrow v (m.drop (measurementCount L.program))
    (if frozen then st else ECDSAAdd.Divsteps.zStep st) ready r.1 hfit
  have keep : ∀ q∈L.active::L.q::z,v.basis q=s.basis q := by
    intro q hq; exact r.2.2 q (List.disjoint_left.mp hbefore hq)
  dsimp only
  rw [windowStep,run_append,run_take]
  refine ⟨step.1,step.2.1,step.2.2.1,?_⟩
  rw [step.2.2.2,(keep L.active (by simp)),(keep L.q (by simp))]
  rw [regValue_congr z v.basis s.basis (fun q hq => keep q (by simp [hq]))]

/-- Lift the actual counter word result on the successful signed window. -/
theorem counterWord_pinned (st : ECDSAAdd.Divsteps.ZState) (frozen : Bool)
    (active swap : Wire) (z : List Wire) (s t : BasisState)
    (hw : 2≤z.length) (ha : s active= !frozen)
    (hq : s swap=decide (0≤st.z ∧ st.g%2=1)) (hzero : frozen=true → st.g=0)
    (hz : signedRegValue z s=st.z)
    (hword : regValue z t=counterWord z.length (s active) (s swap) (regValue z s))
    (hfit : PayloadFits (z.length-1) (if frozen then st else ECDSAAdd.Divsteps.zStep st).z) :
    signedRegValue z t=(if frozen then st else ECDSAAdd.Divsteps.zStep st).z := by
  have relation : s swap=true → s active=true := by
    cases frozen with
    | false => simp_all
    | true => simp_all
  have next : counterNext (s active) (s swap) st.z=
      (if frozen then st else ECDSAAdd.Divsteps.zStep st).z := by
    rw [ha,hq]
    cases frozen with
    | false =>
      simp only [Bool.not_false,counterNext,ite_true,decide_eq_true_eq]
      unfold ECDSAAdd.Divsteps.zStep
      split_ifs <;> first | contradiction | rfl
    | true => simp [counterNext]
  have lift := counterWord_signed z.length (s active) (s swap) (regValue z s) hw
    (regValue_lt z s) relation
    (by change _≤counterNext (s active) (s swap) (signedRegValue z s); rw [hz,next]; exact hfit.1)
    (by change counterNext (s active) (s swap) (signedRegValue z s)<_; rw [hz,next]; exact hfit.2)
  change signedDecode z.length (regValue z t)=_
  rw [hword,lift]
  change counterNext (s active) (s swap) (signedRegValue z s)=_
  rw [hz,next]

def RoutedBankLayout.windowStepInverse (L : RoutedBankLayout) (resize : Program)
    (zero z carry : List Wire) : Program :=
  (counterUpdateInverse L.active L.q zero z carry++resize.reverse)++L.inverse

theorem RoutedBankLayout.windowStep_roundtrip (L : RoutedBankLayout) (hv : L.Valid)
    (out : WindowBank) (w : RowWindow) (A C D : Arena) (resize : Program)
    (hp : L.after.Planned out w A C resize) (z zero carry : List Wire)
    (hn : (L.active::L.q::(zero++z++carry)).Nodup)
    (hz : zero.length=z.length) (hc : carry.length+1=z.length)
    (hrow : (L.before.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (hown : (L.active::L.q::z).toFinset⊆A.live)
    (hbefore : List.Disjoint (L.active::L.q::z) (L.before.rows.flatMap WindowRow.wires))
    (hafter : List.Disjoint (L.active::L.q::z) (L.after.rows.flatMap WindowRow.wires))
    (hborrow : C.reserve (zero++carry).toFinset=some D)
    (st : ECDSAAdd.Divsteps.ZState) (frozen : Bool) (hf : st.f%2=1)
    (s : State) (m n : List Bool) (hu : s.basis L.u=false) (hk : s.basis L.k=false)
    (ha : s.basis L.active= !frozen)
    (hq : s.basis L.q=decide (0≤st.z ∧ st.g%2=1))
    (hb : s.basis L.parity=decide (ECDSAAdd.Divsteps.bbit st=1))
    (he : L.before.Encodes s.basis st) (hzero : frozen=true → st.g=0)
    (hg : frozen=false → PayloadFits (L.gmid.length+1) (2*(ECDSAAdd.Divsteps.zStep st).g))
    (hgv : frozen=false → PayloadFits (L.gv.wires.length-1) (ECDSAAdd.Divsteps.zStep st).gv)
    (hfv : frozen=false → PayloadFits (L.vmid.length+1) (ECDSAAdd.Divsteps.zStep st).fv)
    (hready : A.Ready s.basis) (hfit : w.Fits (if frozen then st else ECDSAAdd.Divsteps.zStep st)) :
    run (L.windowStepInverse resize zero z carry) n
      (run (L.windowStep resize zero z carry) m s)=s := by
  let v := run L.program m s
  have r := L.run_pinned hv st frozen hf s m hu hk ha hq hb he hzero hg hgv hfv
  have ready : A.Ready v.basis := by
    intro q hq hn
    rw [r.2.2 q (fun hh => hn (hrow (List.mem_toFinset.mpr hh)))]
    exact hready q hq hn
  have keep : ∀ q∈L.active::L.q::z,v.basis q=s.basis q := by
    intro q hq; exact r.2.2 q (List.disjoint_left.mp hbefore hq)
  have relation : v.basis L.q=true → v.basis L.active=true := by
    rw [(keep L.q (by simp)),(keep L.active (by simp)),ha,hq]
    cases frozen with
    | false => simp
    | true => simp [hzero rfl]
  have inv := L.after.resize_counter_roundtrip out w A C D resize hp L.active L.q z zero carry
    hn hz hc hown hafter hborrow v (m.drop (measurementCount L.program)) n
    (if frozen then st else ECDSAAdd.Divsteps.zStep st) ready r.1 hfit relation
  rw [windowStep,run_append,run_take,windowStepInverse,run_append,run_take,inv]
  exact L.roundtrip hv s m _ hu hk

end ECDSAAdd.Arithmetic.Paper935
